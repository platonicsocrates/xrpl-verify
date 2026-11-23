(** * The compiled close-time function computes the close-time rule

    [eff_close_time] is nine RISC-V instructions at 0x11018 in the test
    binary: the XRP Ledger's [effCloseTime] with [roundCloseTime] inlined,
    as the compiler emitted them for the types consensus uses.

      11018  beq   a0, zero, 11038     closeTime == 0: return it
      1101c  srliw a3, a1, 1           resolution / 2
      11020  add   a0, a3, a0          closeTime += resolution / 2
      11024  remuw a1, a0, a1          closeTime % resolution
      11028  subw  a0, a0, a1          rounded close time
      1102c  addiw a2, a2, 1           priorCloseTime + 1
      11030  bltu  a2, a0, 11038       max of the two
      11034  addi  a0, a2, 0
      11038  jalr  zero, 0(ra)         return

    The theorem below says: started at 0x11018 with any 32-bit close time,
    resolution and previous close time in a0, a1, a2, the machine reaches the
    return address with [CloseTimeSpec.eff_close_time] of them in a0. It
    reads and writes no memory, and changes no register except a0-a3.

    Proof-side file. The statement is not one of the model's sealed
    statements; it is a lemma the process-level proof uses, and it is stated
    in the model's own step function ([RiscvSemantics.step], through
    [CatSim.msteps]). *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From XrplVerify Require Import HarnessMemImage HarnessCode CloseTimeSpec Word32 SegsApp.

Import ListNotations.
Open Scope bv_scope.

(** A conditional branch inside a chain. [L] is the step lemma for the
    direction taken; the branch condition is left as the first goal. *)
Ltac stepb L F D :=
  chain_step;
  [ reflexivity
  | eapply L; [ exact F | reflexivity | exact D | ]
  | step_simpl ].

Section Code.
Context {fx : FPState}.

(** Whatever follows the image's segments in the run's list. *)
Variable vt : list Segment.

Local Abbreviation segs := (harness_segs ++ vt).
Local Abbreviation FA := (fetch_word_app harness_segs vt _ _).

Lemma v_add_low : forall x y : word,
  (bv_unsigned (v_add x y) mod two32
   = (bv_unsigned x + bv_unsigned y) mod two32)%Z.
Proof.
  intros x y. unfold v_add. rewrite Z_to_bv_unsigned, wrap64. unfold two32.
  Z.div_mod_to_equations; lia.
Qed.

(** What the four arithmetic instructions at 1101c-11028 leave in a0: the
    rounded close time. *)
Lemma rounded_value : forall c r : Z,
  (0 < c < two32)%Z -> (0 < r < two32)%Z ->
  v_subw (v_add (v_srliw (sx32 r) 1) (sx32 c))
         (v_remuw (v_add (v_srliw (sx32 r) 1) (sx32 c)) (sx32 r))
  = sx32 (round_close_time c r).
Proof.
  intros c r Hc Hr.
  assert (Hrmod : (r mod two32 = r)%Z) by (apply Z.mod_small; lia).
  assert (Hhalf : (bv_unsigned (v_srliw (sx32 r) 1) = r / 2)%Z).
  { rewrite (v_srliw1_sx32 _ r) by apply sx32_low. rewrite Hrmod.
    rewrite Z_to_bv_unsigned, wrap64. apply Z.mod_small.
    clear - Hr. unfold two32 in *. Z.div_mod_to_equations; lia. }
  (* the low 32 bits of a0 after the add *)
  assert (V0 : (bv_unsigned (v_add (v_srliw (sx32 r) 1) (sx32 c)) mod two32
                = (c + r / 2) mod two32)%Z).
  { rewrite v_add_low, Hhalf. rewrite Z.add_mod by discriminate.
    rewrite sx32_low. rewrite <- Z.add_mod by discriminate.
    f_equal. apply Z.add_comm. }
  rewrite (v_remuw_sx32 _ _ (c + r / 2) r V0 (sx32_low r))
    by (rewrite Hrmod; clear - Hr; lia).
  rewrite Hrmod.
  rewrite (v_subw_sx32 _ _ (c + r / 2) (((c + r / 2) mod two32) mod r)
             V0 (sx32_low _)).
  apply sx32_congr. unfold round_close_time.
  destruct (c =? 0)%Z eqn:E; [apply Z.eqb_eq in E; clear - Hc E; lia |].
  cbv zeta. rewrite Z.mod_mod by discriminate.
  rewrite Zminus_mod_idemp_l. reflexivity.
Qed.

(** What [addiw a2, a2, 1] leaves in a2: the second after the previous
    close. *)
Lemma next_value : forall p : Z,
  v_addiw (sx32 p) 1 = sx32 ((p + 1) mod two32).
Proof.
  intro p. rewrite (v_addiw_sx32 _ p 1 (sx32_low p)).
  symmetry. apply sx32_mod.
Qed.

Lemma round_close_time_range : forall c r,
  (0 <= round_close_time c r < two32)%Z.
Proof.
  intros c r. unfold round_close_time.
  destruct (c =? 0)%Z; [unfold two32; lia |].
  cbv zeta. apply Z.mod_pos_bound. reflexivity.
Qed.

Theorem eff_close_time_code : forall regs mem rom (c r p : Z) (ra : word),
  (0 <= c < two32)%Z -> (0 < r < two32)%Z -> (0 <= p < two32)%Z ->
  getr regs 10 = sx32 c -> getr regs 11 = sx32 r -> getr regs 12 = sx32 p ->
  getr regs 1 = ra ->
  exists regs',
    msteps segs (mkst regs 0x11018 mem rom) (mkst regs' (v_jalr ra 0) mem rom)
    /\ getr regs' 10 = sx32 (eff_close_time c r p)
    /\ (forall x : reg, x <> 10 -> x <> 11 -> x <> 12 -> x <> 13 ->
          getr regs' x = getr regs x).
Proof.
  intros regs mem rom c r p ra Hc Hr Hp H10 H11 H12 H1.
  destruct (Z.eq_dec c 0) as [Hc0 | Hc0].
  - (* closeTime = 0: the branch at 11018 is taken, straight to the return *)
    subst c. exists regs. split; [| split].
    + stepb step_beq_tk (FA F_11018) D_11018.
      { rewrite H10, getr_zero, <- sx32_zero, sx32_eqb. reflexivity. }
      stepjr (FA F_11038) D_11038 ra ltac:(exact H1).
      apply mst_refl.
    + rewrite H10. reflexivity.
    + intros; reflexivity.
  - (* closeTime <> 0: round, then take the larger of the two *)
    assert (Hne : c_eq (getr regs 10) (getr regs 0) = false).
    { rewrite H10, getr_zero, <- sx32_zero, sx32_eqb.
      apply Z.eqb_neq. rewrite Z.mod_small by exact Hc.
      rewrite Z.mod_small by (unfold two32; lia). exact Hc0. }
    assert (Hc' : (0 < c < two32)%Z) by (clear - Hc Hc0; lia).
    assert (R10 : reg_get regs 10 = sx32 c) by (rewrite <- H10; symmetry; apply getr_nz; reg_neq_tac).
    assert (R11 : reg_get regs 11 = sx32 r) by (rewrite <- H11; symmetry; apply getr_nz; reg_neq_tac).
    assert (R12 : reg_get regs 12 = sx32 p) by (rewrite <- H12; symmetry; apply getr_nz; reg_neq_tac).
    pose proof (rounded_value c r Hc' Hr) as VX.
    pose proof (next_value p) as VQ.
    pose proof (round_close_time_range c r) as Hrr.
    assert (Heff : eff_close_time c r p
                   = Z.max (round_close_time c r) ((p + 1) mod two32)).
    { unfold eff_close_time.
      destruct (c =? 0)%Z eqn:E; [apply Z.eqb_eq in E; contradiction | reflexivity]. }
    assert (Hcmp : c_ltu (sx32 ((p + 1) mod two32)) (sx32 (round_close_time c r))
                   = ((p + 1) mod two32 <? round_close_time c r)%Z).
    { rewrite sx32_ltu. rewrite Z.mod_mod by discriminate.
      rewrite (Z.mod_small (round_close_time c r)) by exact Hrr. reflexivity. }
    destruct ((p + 1) mod two32 <? round_close_time c r)%Z eqn:Elt.
    + (* previous close + 1 is smaller: keep the rounded time *)
      eexists. split; [| split].
      * stepb step_beq_ft (FA F_11018) D_11018. { exact Hne. }
        stepi (FA F_1101c) D_1101c. getr_resolve. imm_norm. rewrite ?R10, ?R11, ?R12.
        stepi (FA F_11020) D_11020. getr_resolve. imm_norm. rewrite ?R10, ?R11, ?R12.
        stepi (FA F_11024) D_11024. getr_resolve. imm_norm. rewrite ?R10, ?R11, ?R12.
        stepi (FA F_11028) D_11028. getr_resolve. imm_norm. rewrite ?R10, ?R11, ?R12.
        rewrite VX.
        stepi (FA F_1102c) D_1102c. getr_resolve. imm_norm. rewrite ?R10, ?R11, ?R12.
        rewrite VQ.
        stepb step_bltu_tk (FA F_11030) D_11030.
        { getr_resolve. exact Hcmp. }
        stepjr (FA F_11038) D_11038 ra ltac:(getr_resolve; exact H1).
        apply mst_refl.
      * getr_resolve. rewrite Heff. f_equal.
        apply Z.ltb_lt in Elt. clear - Elt. lia.
      * intros y Hy10 Hy11 Hy12 Hy13.
        rewrite !getr_other by assumption. reflexivity.
    + (* otherwise: the second after the previous close *)
      eexists. split; [| split].
      * stepb step_beq_ft (FA F_11018) D_11018. { exact Hne. }
        stepi (FA F_1101c) D_1101c. getr_resolve. imm_norm. rewrite ?R10, ?R11, ?R12.
        stepi (FA F_11020) D_11020. getr_resolve. imm_norm. rewrite ?R10, ?R11, ?R12.
        stepi (FA F_11024) D_11024. getr_resolve. imm_norm. rewrite ?R10, ?R11, ?R12.
        stepi (FA F_11028) D_11028. getr_resolve. imm_norm. rewrite ?R10, ?R11, ?R12.
        rewrite VX.
        stepi (FA F_1102c) D_1102c. getr_resolve. imm_norm. rewrite ?R10, ?R11, ?R12.
        rewrite VQ.
        stepb step_bltu_ft (FA F_11030) D_11030.
        { getr_resolve. exact Hcmp. }
        stepi (FA F_11034) D_11034. getr_resolve. rewrite v_addi_0.
        stepjr (FA F_11038) D_11038 ra ltac:(getr_resolve; exact H1).
        apply mst_refl.
      * getr_resolve. rewrite Heff. f_equal.
        apply Z.ltb_ge in Elt. clear - Elt. lia.
      * intros y Hy10 Hy11 Hy12 Hy13.
        rewrite !getr_other by assumption. reflexivity.
Qed.

End Code.
