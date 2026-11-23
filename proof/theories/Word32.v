(** * 32-bit values in 64-bit registers

    RV64 keeps a 32-bit integer in a 64-bit register sign-extended, and the
    "W" instructions ([addw], [subw], [remuw], ...) compute on the low 32
    bits and sign-extend the result. [sx32 z] is the register that holds the
    32-bit value [z mod 2^32]. The lemmas here say what the model's value
    forms do to such registers. Proof-side file: nothing here is trusted. *)

From Stdlib Require Import ZArith Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From LinuxProcessSemantics.Common Require Import PropExec SeqExec.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From XrplVerify Require Import CloseTimeSpec.

Local Open Scope Z_scope.

Definition sx32 (z : Z) : word := Z_to_bv 64 (bv_swrap 32 z).

(** Case-split every integer comparison in the goal, then finish by linear
    arithmetic. *)
Ltac zbool :=
  repeat match goal with
         | |- context [?a <? ?b] => destruct (Z.ltb_spec a b)
         | |- context [?a =? ?b] => destruct (Z.eqb_spec a b)
         end;
  first [reflexivity | exfalso; lia | lia].

Lemma wrap32 : forall z, bv_wrap 32 z = z mod two32.
Proof. reflexivity. Qed.

Lemma wrap64 : forall z, bv_wrap 64 z = z mod 18446744073709551616.
Proof. reflexivity. Qed.

Lemma swrap32 : forall z,
  bv_swrap 32 z = if z mod two32 <? 2147483648 then z mod two32
                  else z mod two32 - two32.
Proof.
  intro z. unfold bv_swrap. rewrite wrap32.
  change (bv_half_modulus 32) with 2147483648. unfold two32.
  destruct (z mod 4294967296 <? 2147483648) eqn:E;
    [apply Z.ltb_lt in E | apply Z.ltb_ge in E];
    Z.div_mod_to_equations; lia.
Qed.

(** The unsigned 64-bit reading of a sign-extended 32-bit value. *)
Lemma sx32_unsigned : forall z,
  bv_unsigned (sx32 z)
  = if z mod two32 <? 2147483648 then z mod two32
    else z mod two32 + (18446744073709551616 - two32).
Proof.
  intro z. unfold sx32. rewrite Z_to_bv_unsigned, wrap64, swrap32.
  pose proof (Z.mod_pos_bound z two32 eq_refl) as Hb. unfold two32 in *.
  destruct (z mod 4294967296 <? 2147483648) eqn:E;
    [apply Z.ltb_lt in E | apply Z.ltb_ge in E].
  - apply Z.mod_small. lia.
  - Z.div_mod_to_equations; lia.
Qed.

(** Its low 32 bits are the value. *)
Lemma sx32_low : forall z, bv_unsigned (sx32 z) mod two32 = z mod two32.
Proof.
  intro z. rewrite sx32_unsigned.
  pose proof (Z.mod_pos_bound z two32 eq_refl) as Hb. unfold two32 in *.
  destruct (z mod 4294967296 <? 2147483648);
    Z.div_mod_to_equations; lia.
Qed.

(** [sx32] only looks at the low 32 bits. *)
Lemma sx32_congr : forall a b, a mod two32 = b mod two32 -> sx32 a = sx32 b.
Proof.
  intros a b H. unfold sx32. f_equal. rewrite !swrap32, H. reflexivity.
Qed.

Lemma sx32_mod : forall z, sx32 (z mod two32) = sx32 z.
Proof. intro z. apply sx32_congr. apply Z.mod_mod. discriminate. Qed.

Lemma sx32_small : forall z, 0 <= z < 2147483648 -> sx32 z = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite swrap32. unfold two32.
  rewrite Z.mod_small by lia.
  destruct (z <? 2147483648) eqn:E; [reflexivity | apply Z.ltb_ge in E; lia].
Qed.

(** Unsigned 64-bit comparison of two sign-extended 32-bit values is the
    unsigned comparison of the 32-bit values. This is what lets the compiler
    use [bltu] on whole registers. *)
Lemma sx32_ltu : forall a b,
  c_ltu (sx32 a) (sx32 b) = (a mod two32 <? b mod two32).
Proof.
  intros a b. unfold c_ltu, bv_ltu. rewrite !sx32_unsigned.
  pose proof (Z.mod_pos_bound a two32 eq_refl) as Ha.
  pose proof (Z.mod_pos_bound b two32 eq_refl) as Hb. unfold two32 in *.
  destruct (Z.ltb_spec (a mod 4294967296) 2147483648);
    destruct (Z.ltb_spec (b mod 4294967296) 2147483648); zbool.
Qed.

Lemma sx32_eqb : forall a b,
  c_eq (sx32 a) (sx32 b) = (a mod two32 =? b mod two32).
Proof.
  intros a b. unfold c_eq, bv_eqb. rewrite !sx32_unsigned.
  pose proof (Z.mod_pos_bound a two32 eq_refl) as Ha.
  pose proof (Z.mod_pos_bound b two32 eq_refl) as Hb. unfold two32 in *.
  destruct (Z.ltb_spec (a mod 4294967296) 2147483648);
    destruct (Z.ltb_spec (b mod 4294967296) 2147483648); zbool.
Qed.

Lemma sx32_zero : sx32 0 = Z_to_bv 64 0.
Proof. apply sx32_small. lia. Qed.

(* ------------------------------------------------------------------------- *)
(** ** The value forms the close-time code uses *)

(** [addw], [subw], [addiw]: add or subtract, keep the low 32 bits. *)
Lemma v_addw_sx32 : forall x y a b,
  bv_unsigned x mod two32 = a mod two32 ->
  bv_unsigned y mod two32 = b mod two32 ->
  v_addw x y = sx32 (a + b).
Proof.
  intros x y a b Hx Hy. unfold v_addw. fold (sx32 (bv_unsigned x + bv_unsigned y)).
  apply sx32_congr. rewrite Z.add_mod, Hx, Hy, <- Z.add_mod; [reflexivity | | ];
    discriminate.
Qed.

Lemma v_subw_sx32 : forall x y a b,
  bv_unsigned x mod two32 = a mod two32 ->
  bv_unsigned y mod two32 = b mod two32 ->
  v_subw x y = sx32 (a - b).
Proof.
  intros x y a b Hx Hy. unfold v_subw. fold (sx32 (bv_unsigned x - bv_unsigned y)).
  apply sx32_congr. rewrite Zminus_mod, Hx, Hy, <- Zminus_mod. reflexivity.
Qed.

Lemma v_addiw_sx32 : forall x a k,
  bv_unsigned x mod two32 = a mod two32 ->
  v_addiw x k = sx32 (a + k).
Proof.
  intros x a k Hx. unfold v_addiw. fold (sx32 (bv_unsigned x + k)).
  apply sx32_congr. rewrite Z.add_mod, Hx, <- Z.add_mod; [reflexivity | | ];
    discriminate.
Qed.

(** [srliw x, 1]: halve the low 32 bits. *)
Lemma v_srliw1_sx32 : forall x a,
  bv_unsigned x mod two32 = a mod two32 ->
  v_srliw x 1 = Z_to_bv 64 (a mod two32 / 2).
Proof.
  intros x a Hx. unfold v_srliw. rewrite wrap32, Hx, Z.shiftr_div_pow2 by lia.
  change (2 ^ 1) with 2. fold (sx32 (a mod two32 / 2)).
  apply sx32_small.
  pose proof (Z.mod_pos_bound a two32 eq_refl) as Hb. unfold two32 in *.
  Z.div_mod_to_equations; lia.
Qed.

(** [remuw]: unsigned remainder of the low 32 bits. *)
Lemma v_remuw_sx32 : forall x y a b,
  bv_unsigned x mod two32 = a mod two32 ->
  bv_unsigned y mod two32 = b mod two32 ->
  b mod two32 <> 0 ->
  v_remuw x y = sx32 ((a mod two32) mod (b mod two32)).
Proof.
  intros x y a b Hx Hy Hb. unfold v_remuw. rewrite !wrap32, Hx, Hy.
  destruct (b mod two32 =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction |].
  reflexivity.
Qed.

(* ------------------------------------------------------------------------- *)
(** ** The value forms the test's own code uses *)

Lemma u64_small : forall z, 0 <= z < 18446744073709551616 ->
  bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned, wrap64. apply Z.mod_small. exact Hz. Qed.

(** [slli x, 32] then [srli x, 32]: zero-extend the low 32 bits. *)
Lemma zext32_sx32 : forall z,
  v_srli (v_slli (sx32 z) 32) 32 = Z_to_bv 64 (z mod two32).
Proof.
  intro z. unfold v_srli, v_slli. rewrite Z_to_bv_unsigned, wrap64.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. f_equal.
  rewrite <- (sx32_low z).
  pose proof (bv_unsigned_in_range _ (sx32 z)) as Hr.
  change (bv_modulus 64) with 18446744073709551616 in Hr.
  unfold two32. change (2 ^ 32) with 4294967296.
  generalize dependent (bv_unsigned (sx32 z)). intros u Hr.
  Z.div_mod_to_equations; lia.
Qed.

Lemma c_ltu_small : forall a b,
  0 <= a < 18446744073709551616 -> 0 <= b < 18446744073709551616 ->
  c_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof.
  intros a b Ha Hb. unfold c_ltu, bv_ltu. rewrite !u64_small by assumption.
  reflexivity.
Qed.

Lemma c_eq_small : forall a b,
  0 <= a < 18446744073709551616 -> 0 <= b < 18446744073709551616 ->
  c_eq (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u64_small by assumption.
  reflexivity.
Qed.

Lemma v_add_lit : forall a b,
  0 <= a < 18446744073709551616 -> 0 <= b < 18446744073709551616 ->
  v_add (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b Ha Hb. unfold v_add. rewrite !u64_small by assumption. reflexivity.
Qed.

(** A multiple of 16 has no bit in common with a number below 16. *)
Lemma lor_low4 : forall q n, 0 <= q -> 0 <= n < 16 ->
  Z.lor (16 * q) n = 16 * q + n.
Proof.
  intros q n Hq Hn.
  assert (Hland : Z.land (16 * q) n = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.ltb_spec i 4).
    - replace (16 * q) with (Z.shiftl q 4) by (rewrite Z.shiftl_mul_pow2; lia).
      rewrite Z.shiftl_spec_low by lia. reflexivity.
    - destruct (Z.eq_dec n 0) as [-> | Hn0];
        [rewrite Z.bits_0; apply andb_false_r |].
      rewrite (Z.bits_above_log2 n i); [apply andb_false_r | lia |].
      apply Z.lt_le_trans with 4; [| exact H].
      apply Z.log2_lt_pow2; [lia |]. change (2 ^ 4) with 16. lia. }
  pose proof (Z.add_lor_land (16 * q) n) as Hadd. rewrite Hland in Hadd. lia.
Qed.

(** One round of the test's input decoding: shift the accumulator left by
    four bits, in 32 bits, and put the low four bits of a character below.
    Whatever went in, what comes out is some 32-bit value, sign-extended. *)
Lemma nibble_acc : forall (x : word) (b : byte),
  exists a, 0 <= a < two32
    /\ v_or (v_slliw x 4) (v_andi (Z_to_bv 64 (bv_unsigned b)) 15) = sx32 a.
Proof.
  intros x b.
  pose proof (bv_unsigned_in_range _ b) as Hb.
  change (bv_modulus 8) with 256 in Hb.
  set (n := Z.land (bv_unsigned b) 15).
  assert (Hn : 0 <= n < 16).
  { unfold n. change 15 with (Z.ones 4). rewrite Z.land_ones by lia.
    change (2 ^ 4) with 16. apply Z.mod_pos_bound. lia. }
  set (w := (bv_unsigned x * 16) mod two32).
  assert (Hw : 0 <= w < two32 /\ w mod 16 = 0).
  { unfold w, two32. Z.div_mod_to_equations; lia. }
  exists (w + n). split; [unfold two32 in *; Z.div_mod_to_equations; lia |].
  (* the shifted accumulator *)
  assert (HA : v_slliw x 4 = sx32 (bv_unsigned x * 16)).
  { unfold v_slliw. rewrite Z.shiftl_mul_pow2 by lia. reflexivity. }
  (* the masked character *)
  assert (HB : bv_unsigned (v_andi (Z_to_bv 64 (bv_unsigned b)) 15) = n).
  { unfold v_andi. rewrite (u64_small (bv_unsigned b)) by lia.
    change (bv_wrap 64 15) with 15. fold n. apply u64_small. lia. }
  unfold v_or. rewrite HA, HB, sx32_unsigned. fold w.
  apply bv_eq. unfold sx32. rewrite !Z_to_bv_unsigned, !wrap64, swrap32.
  destruct Hw as [Hw Hw16].
  assert (Hwn : (w + n) mod two32 = w + n)
    by (apply Z.mod_small; unfold two32 in *; Z.div_mod_to_equations; lia).
  rewrite Hwn.
  destruct (Z.ltb_spec w 2147483648) as [Hlt | Hge].
  - replace w with (16 * (w / 16)) at 1 by (Z.div_mod_to_equations; lia).
    rewrite lor_low4 by (try exact Hn; Z.div_mod_to_equations; lia).
    replace (16 * (w / 16)) with w by (Z.div_mod_to_equations; lia).
    destruct (Z.ltb_spec (w + n) 2147483648); [reflexivity |].
    exfalso. Z.div_mod_to_equations; lia.
  - replace (w + (18446744073709551616 - two32))
      with (16 * ((w + (18446744073709551616 - two32)) / 16))
      by (unfold two32 in *; Z.div_mod_to_equations; lia).
    rewrite lor_low4 by (try exact Hn; unfold two32 in *; Z.div_mod_to_equations; lia).
    replace (16 * ((w + (18446744073709551616 - two32)) / 16))
      with (w + (18446744073709551616 - two32))
      by (unfold two32 in *; Z.div_mod_to_equations; lia).
    destruct (Z.ltb_spec (w + n) 2147483648);
      [exfalso; lia |].
    unfold two32 in *. Z.div_mod_to_equations; lia.
Qed.
