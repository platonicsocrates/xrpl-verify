(** * The close-time rule, as mathematics

    This file has no machine code in it. It states, over the integers, what
    the XRP Ledger's [roundCloseTime] and [effCloseTime] compute
    (include/xrpl/ledger/LedgerTiming.h), and proves the properties the
    protocol relies on. [CloseTimeCode.v] then proves that the compiled
    RISC-V instructions compute exactly these functions.

    Times are whole seconds since 2000-01-01 UTC, held in 32 bits
    ([NetClock::rep] is [std::uint32_t]), so every operation wraps at 2^32.
    The definitions below keep that wrapping. *)

From Stdlib Require Import ZArith List Lia.
Import ListNotations.
Open Scope Z_scope.

Definition two32 : Z := 4294967296.

(** The six close-time resolutions the protocol allows, in seconds
    ([kLedgerPossibleTimeResolutions]). *)
Definition resolutions : list Z := [10; 20; 30; 60; 90; 120].

(** [roundCloseTime(closeTime, closeResolution)]:

      if (closeTime == time_point{}) return closeTime;
      closeTime += (closeResolution / 2);
      return closeTime - (closeTime.time_since_epoch() % closeResolution); *)
Definition round_close_time (c r : Z) : Z :=
  if c =? 0 then 0
  else let x := (c + r / 2) mod two32 in (x - x mod r) mod two32.

(** [effCloseTime(closeTime, resolution, priorCloseTime)]:

      if (closeTime == time_point{}) return closeTime;
      return std::max(roundCloseTime(closeTime, resolution), priorCloseTime + 1s); *)
Definition eff_close_time (c r p : Z) : Z :=
  if c =? 0 then 0
  else Z.max (round_close_time c r) ((p + 1) mod two32).

(** The last second at which no step above can wrap, for any legal
    resolution: 2^32 - 1 - 60, which is 06:27:15 UTC on 7 February 2136. *)
Definition horizon : Z := two32 - 1 - 60.

Ltac legal_resolution H :=
  cbv [resolutions In] in H;
  repeat (destruct H as [H | H]; [subst | ]); [ .. | contradiction ].

(* ------------------------------------------------------------------------- *)
(** ** What the rule guarantees *)

(** A close time of zero means "no close time". It passes through. *)
Theorem eff_zero : forall r p, eff_close_time 0 r p = 0.
Proof. reflexivity. Qed.

(** The result always fits in 32 bits. *)
Theorem eff_range : forall c r p, 0 <= eff_close_time c r p < two32.
Proof.
  intros c r p. unfold eff_close_time, round_close_time, two32.
  destruct (c =? 0); [lia |].
  cbv zeta.
  pose proof (Z.mod_pos_bound ((c + r / 2) mod 4294967296
                               - ((c + r / 2) mod 4294967296) mod r) 4294967296).
  pose proof (Z.mod_pos_bound (p + 1) 4294967296). lia.
Qed.

(** If adding half the resolution does not wrap, rounding is rounding: the
    nearest multiple of the resolution, and up on a tie. *)
Lemma round_no_wrap : forall c r,
  0 < r -> 0 < c -> c + r / 2 < two32 ->
  round_close_time c r = r * ((c + r / 2) / r).
Proof.
  intros c r Hr Hc Hx. unfold round_close_time.
  destruct (c =? 0) eqn:E; [apply Z.eqb_eq in E; lia |].
  cbv zeta.
  assert (Hh : 0 <= r / 2) by (apply Z.div_pos; lia).
  rewrite (Z.mod_small (c + r / 2)) by lia.
  pose proof (Z.div_mod (c + r / 2) r ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound (c + r / 2) r Hr) as Hm.
  replace (c + r / 2 - (c + r / 2) mod r) with (r * ((c + r / 2) / r)) by lia.
  apply Z.mod_small. split; [| lia].
  apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia].
Qed.

(** If it does wrap, the "rounded" time is zero: the first second of 2000. *)
Lemma round_wrap : forall c r,
  In r resolutions -> 0 < c < two32 -> two32 <= c + r / 2 ->
  round_close_time c r = 0.
Proof.
  intros c r Hr Hc Hx. unfold round_close_time, two32 in *.
  destruct (c =? 0) eqn:E; [reflexivity |].
  legal_resolution Hr; cbv zeta;
    change (10 / 2) with 5 in *; change (20 / 2) with 10 in *;
    change (30 / 2) with 15 in *; change (60 / 2) with 30 in *;
    change (90 / 2) with 45 in *; change (120 / 2) with 60 in *;
    Z.div_mod_to_equations; lia.
Qed.

Lemma legal_resolution_bounds : forall r,
  In r resolutions -> 0 < r /\ r / 2 <= 60.
Proof. intros r Hr. legal_resolution Hr; cbv; split; congruence. Qed.

(** Before the horizon, rounding is rounding. *)
Theorem round_nearest : forall c r,
  In r resolutions -> 0 < c <= horizon ->
  round_close_time c r = r * ((c + r / 2) / r).
Proof.
  intros c r Hr Hc. destruct (legal_resolution_bounds r Hr) as [Hr0 Hh].
  apply round_no_wrap; unfold horizon, two32 in *; lia.
Qed.

(** A ledger closes strictly after the ledger before it. The previous close
    time must not be the counter's last second. *)
Theorem eff_after_prior : forall c r p,
  0 < c < two32 -> 0 <= p < two32 - 1 ->
  p < eff_close_time c r p.
Proof.
  intros c r p Hc Hp. unfold eff_close_time, two32 in *.
  destruct (c =? 0) eqn:E; [apply Z.eqb_eq in E; lia |].
  rewrite (Z.mod_small (p + 1)) by lia. lia.
Qed.

(** The result is the second after the previous close, or it is on a
    resolution boundary within half a resolution of the raw close time.

    This needs no bound on the close time. Where the rounding wraps, it
    gives zero, and zero loses to "previous close + 1". *)
Theorem eff_on_boundary : forall c r p,
  In r resolutions -> 0 < c < two32 -> 0 <= p < two32 - 1 ->
  eff_close_time c r p = p + 1
  \/ (eff_close_time c r p mod r = 0
      /\ c - r / 2 <= eff_close_time c r p <= c + r / 2).
Proof.
  intros c r p Hr Hc Hp.
  destruct (legal_resolution_bounds r Hr) as [Hr0 Hh].
  assert (Hnext : (p + 1) mod two32 = p + 1)
    by (apply Z.mod_small; unfold two32 in *; lia).
  unfold eff_close_time.
  destruct (c =? 0) eqn:E; [apply Z.eqb_eq in E; lia |].
  rewrite Hnext.
  destruct (Z.lt_ge_cases (c + r / 2) two32) as [Hfit | Hwrap].
  - (* the rounding does not wrap *)
    rewrite (round_no_wrap c r Hr0 ltac:(lia) Hfit).
    destruct (Z.max_spec (r * ((c + r / 2) / r)) (p + 1)) as [[_ Hm] | [_ Hm]];
      rewrite Hm; [left; reflexivity | right].
    split; [rewrite Z.mul_comm; apply Z.mod_mul; lia |].
    pose proof (Z.div_mod (c + r / 2) r ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (c + r / 2) r Hr0) as Hmb.
    pose proof (Z.div_mod r 2 ltac:(lia)) as Hr2.
    pose proof (Z.mod_pos_bound r 2 ltac:(lia)) as Hr2b.
    lia.
  - (* it wraps: the rounded time is 0, so the result is p + 1 *)
    rewrite (round_wrap c r Hr Hc Hwrap). left. lia.
Qed.

(* ------------------------------------------------------------------------- *)
(** ** Where the 32-bit counter shows

    These are not new findings: 32-bit seconds from 2000 run out in 2136 by
    design. They are here because they are exactly where the theorems above
    stop, and the proofs do not go through without the bounds. *)

(** One second before the counter runs out, rounding to 30 s lands in the
    year 2000. So [round_nearest] needs its horizon. *)
Example round_wraps_past_horizon : round_close_time 4294967295 30 = 0.
Proof. reflexivity. Qed.

(** The horizon is the largest bound that serves every legal resolution: one
    second past it, rounding to 120 s wraps. *)
Example round_wraps_just_past_horizon :
  round_close_time (horizon + 1) 120 = 0.
Proof. reflexivity. Qed.

(** If the previous ledger closed in the counter's last second, the next
    close time is not after it. So [eff_after_prior] needs its bound. *)
Example eff_not_after_prior_at_the_end :
  eff_close_time 100 30 4294967295 = 90.
Proof. reflexivity. Qed.
