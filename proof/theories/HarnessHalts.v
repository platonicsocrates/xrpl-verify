(** * The test binary halts with status 0 on every input

    PROOF-SIDE FILE. *)

From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Common Require Import ExitSim PropExec CatExec CatSim SeqExec StepTac StoreOk ArgvEnv WxExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From XrplVerify Require Import HarnessMemImage HarnessCode CloseTimeSpec Word32 SegsApp CloseTimeCode.
Import ListNotations.
Open Scope bv_scope.
Set Default Timeout 600.

(** The floating-point state at process start. The test has no
    floating-point instruction, so it never changes. *)
#[local] Instance fx : FPState := fx0.

Section Run.

(** One launch of the program: everything the process receives (arguments,
    environment, files, ...), where the kernel put the stack, the program
    break and the mmap base, and the kernel's random draw. All of it is
    arbitrary; the hypotheses are the model's definition of a valid launch. *)
Variable inp : ProcInput.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hvl : valid_launch inp.
Variable sp brk mb : word.
Variable rnd : EntryDraw.
Hypothesis Hsp_lo : (sp_window_lo <= bv_unsigned sp)%Z.
Hypothesis Hsp_hi : (bv_unsigned sp <= sp_window_hi)%Z.
Hypothesis Hlaunch : entry_launch_ok_va Sv48 (mkEntry sp brk mb rnd) inp.

(** The entry address the kernel writes in the auxiliary vector. The test
    never reads it. *)
Variable entry : word.

Local Abbreviation vt := (vdso_segments (in_kernel inp) sp mb).
Local Abbreviation segs := (harness_segs ++ vt).
Local Abbreviation FA := (fetch_word_app harness_segs vt _ _).
Local Abbreviation rom := (seg_rom segs).
Local Abbreviation image := (entry_stack_image inp mb harness_phdrs entry sp rnd).
Local Abbreviation M0 := (wrap_mem inp mb harness_phdrs entry sp rnd).

Lemma Hlo : (0x7fff80000000 <= bv_unsigned sp)%Z.
Proof. exact Hsp_lo. Qed.
Lemma Hhi : (bv_unsigned sp <= 0x800000000000)%Z.
Proof. exact Hsp_hi. Qed.

(** [slot k] is the address [k] bytes below the initial stack pointer. *)
Definition slot (k : Z) : word := Z_to_bv 64 (bv_unsigned sp - k).

Lemma u_slot : forall k, (0 <= k <= 4096)%Z ->
  bv_unsigned (slot k) = (bv_unsigned sp - k)%Z.
Proof.
  intros k Hk. pose proof Hlo. pose proof Hhi. unfold slot. apply u_Z2bv; lia.
Qed.

Lemma slot_addi : forall k j, (0 <= k <= 4096)%Z -> (0 <= k - j <= 4096)%Z ->
  v_addi (slot k) j = slot (k - j).
Proof.
  intros k j Hk Hj. unfold v_addi. rewrite u_slot by exact Hk.
  unfold slot. f_equal. lia.
Qed.

(** Where [_start]'s call to [main] returns. *)
Definition ret_start : word := Z_to_bv 64 0x11010.

Section Frame.

(** The three callee-saved registers [main] spills, whatever they hold. *)
Variables v8 v9 v18 : word.

(** Memory once [main] has built its frame: the initial stack, plus the
    four words [main] saved below it. Nothing is stored after that. *)
Definition fmem : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes M0 (slot 8) (word_to_le_bytes 8 ret_start))
                         (slot 16) (word_to_le_bytes 8 v8))
                 (slot 24) (word_to_le_bytes 8 v9))
         (slot 32) (word_to_le_bytes 8 v18).

(** At and above the initial stack pointer, the frame changes nothing. *)
Lemma rdn_fmem_above : forall (a : word) n,
  (bv_unsigned sp <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= 2^64)%Z ->
  rdn segs fmem a n = rdn segs (stack_to_mem sp image) a n.
Proof.
  intros a n Ha Hn. unfold fmem.
  do 4 (rewrite rdn_wbytes_disjoint
          by (rewrite ?length_word_to_le_bytes; repeat rewrite u_slot by lia; lia)).
  apply rdn_wrap_stack_above; assumption.
Qed.

(** The four saved words read back. *)
Lemma rdn_slot8 : rdn segs fmem (slot 8) 8 = Some (word_to_le_bytes 8 ret_start).
Proof.
  pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. unfold fmem.
  do 3 (rewrite rdn_wbytes_disjoint
          by (rewrite ?length_word_to_le_bytes; repeat rewrite u_slot by lia; lia)).
  apply rdn_wbytes_hit8. rewrite u_slot by lia. lia.
Qed.

Lemma rdn_slot16 : rdn segs fmem (slot 16) 8 = Some (word_to_le_bytes 8 v8).
Proof.
  pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. unfold fmem.
  do 2 (rewrite rdn_wbytes_disjoint
          by (rewrite ?length_word_to_le_bytes; repeat rewrite u_slot by lia; lia)).
  apply rdn_wbytes_hit8. rewrite u_slot by lia. lia.
Qed.

Lemma rdn_slot24 : rdn segs fmem (slot 24) 8 = Some (word_to_le_bytes 8 v9).
Proof.
  pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. unfold fmem.
  do 1 (rewrite rdn_wbytes_disjoint
          by (rewrite ?length_word_to_le_bytes; repeat rewrite u_slot by lia; lia)).
  apply rdn_wbytes_hit8. rewrite u_slot by lia. lia.
Qed.

Lemma rdn_slot32 : rdn segs fmem (slot 32) 8 = Some (word_to_le_bytes 8 v18).
Proof.
  pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. unfold fmem.
  apply rdn_wbytes_hit8. rewrite u_slot by lia. lia.
Qed.

(** ** The way out

    Every path that does not trap ends at 0x11140: restore the saved
    registers, return to [_start], and call exit(0). *)
Lemma epilogue : forall regs,
  getr regs 2 = slot 32 ->
  to_wexit segs (mkst regs 0x11140 fmem rom) [] (Z_to_bv 64 0).
Proof.
  intros regs H2.
  assert (R2 : reg_get regs 2 = slot 32)
    by (rewrite <- H2; symmetry; apply getr_nz; reg_neq_tac).
  (* 11140 addi a0, zero, 0 *)
  stepiv (FA F_11140) D_11140 (Z_to_bv 64 0) ltac:(getr_resolve; imm_norm; bveq).
  (* 11144 ld ra, 24(sp) *)
  chain_step;
    [ reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 ret_start) (v := ret_start);
      [ exact (FA F_11144) | reflexivity | exact D_11144
      | getr_resolve; imm_norm; rewrite R2, slot_addi by lia; exact rdn_slot8
      | exact (bytes_le_to_Z_8 _) ]
    | step_simpl ].
  (* 11148 ld s0, 16(sp) *)
  chain_step;
    [ reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 v8) (v := v8);
      [ exact (FA F_11148) | reflexivity | exact D_11148
      | getr_resolve; imm_norm; rewrite R2, slot_addi by lia; exact rdn_slot16
      | exact (bytes_le_to_Z_8 _) ]
    | step_simpl ].
  (* 1114c ld s1, 8(sp) *)
  chain_step;
    [ reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 v9) (v := v9);
      [ exact (FA F_1114c) | reflexivity | exact D_1114c
      | getr_resolve; imm_norm; rewrite R2, slot_addi by lia; exact rdn_slot24
      | exact (bytes_le_to_Z_8 _) ]
    | step_simpl ].
  (* 11150 ld s2, 0(sp) *)
  chain_step;
    [ reflexivity
    | eapply step_ld with (bs := word_to_le_bytes 8 v18) (v := v18);
      [ exact (FA F_11150) | reflexivity | exact D_11150
      | getr_resolve; imm_norm; rewrite R2, slot_addi by lia; exact rdn_slot32
      | exact (bytes_le_to_Z_8 _) ]
    | step_simpl ].
  (* 11154 addi sp, sp, 32 *)
  stepi (FA F_11154) D_11154.
  (* 11158 jalr zero, 0(ra) *)
  stepjr (FA F_11158) D_11158 ret_start ltac:(getr_resolve; reflexivity).
  (* 11010 addi a7, zero, 93 *)
  stepiv (FA F_11010) D_11010 (Z_to_bv 64 93) ltac:(getr_resolve; imm_norm; bveq).
  (* 11014 ecall: exit(a0) *)
  chain_step;
    [ reflexivity
    | apply (step_ecall _ _ _ _ _ _ (FA F_11014) eq_refl)
    | ].
  apply tw_exit_coden.
  - getr_resolve; regupd_resolve; u_norm; lia.
  - regupd_resolve; reflexivity.
  - u_norm; lia.
Qed.

(** ** After the call: the test's own checks

    At 0x110fc the code under test has returned. s0, s1 and s2 hold the
    close time, the previous close time and the resolution; a0 holds the
    result. Each check that could trap is decided here by a theorem of
    [CloseTimeSpec], so the trap at 0x11138 is never reached. *)
Lemma check_block : forall regs (c r p : Z),
  In r resolutions -> (0 <= c <= horizon)%Z -> (0 <= p <= horizon)%Z ->
  getr regs 2 = slot 32 ->
  getr regs 8 = sx32 c -> getr regs 9 = sx32 p -> getr regs 18 = sx32 r ->
  getr regs 10 = sx32 (eff_close_time c r p) ->
  to_wexit segs (mkst regs 0x110fc fmem rom) [] (Z_to_bv 64 0).
Proof.
  intros regs c r p Hr Hc Hp H2 H8 H9 H18 H10.
  pose proof (eff_range c r p) as He.
  assert (Hr' : (0 < r <= 120)%Z) by (clear - Hr; legal_resolution Hr; lia).
  assert (Hhalf : (0 <= r / 2 <= 60)%Z) by (clear - Hr'; Z.div_mod_to_equations; lia).
  assert (R8 : reg_get regs 8 = sx32 c)
    by (rewrite <- H8; symmetry; apply getr_nz; reg_neq_tac).
  assert (R9 : reg_get regs 9 = sx32 p)
    by (rewrite <- H9; symmetry; apply getr_nz; reg_neq_tac).
  assert (R18 : reg_get regs 18 = sx32 r)
    by (rewrite <- H18; symmetry; apply getr_nz; reg_neq_tac).
  assert (R10 : reg_get regs 10 = sx32 (eff_close_time c r p))
    by (rewrite <- H10; symmetry; apply getr_nz; reg_neq_tac).
  assert (R2 : reg_get regs 2 = slot 32)
    by (rewrite <- H2; symmetry; apply getr_nz; reg_neq_tac).
  destruct (Z.eq_dec c 0) as [Hc0 | Hc0].
  - (* no close time: the result must be zero, and it is *)
    subst c.
    stepb step_beq_tk (FA F_110fc) D_110fc.
    { rewrite H8, getr_zero, <- sx32_zero, sx32_eqb. reflexivity. }
    stepb step_bne_ft (FA F_1113c) D_1113c.
    { rewrite H10, getr_zero, eff_zero, <- sx32_zero, sx32_eqb. reflexivity. }
    apply epilogue. exact H2.
  - assert (Hc1 : (0 < c <= horizon)%Z) by (clear - Hc Hc0; lia).
    assert (Hc2 : (0 < c < two32)%Z) by (clear - Hc1; unfold horizon, two32 in *; lia).
    assert (Hp2 : (0 <= p < two32 - 1)%Z) by (clear - Hp; unfold horizon, two32 in *; lia).
    pose proof (eff_after_prior c r p Hc2 Hp2) as Hafter.
    pose proof (eff_on_boundary c r p Hr Hc2 Hp2) as Hbound.
    set (e := eff_close_time c r p) in *.
    assert (Hem : (e mod two32 = e)%Z) by (apply Z.mod_small; exact He).
    assert (Hcm : (c mod two32 = c)%Z) by (apply Z.mod_small; clear - Hc2; lia).
    assert (Hpm : (p mod two32 = p)%Z) by (apply Z.mod_small; clear - Hp2; lia).
    assert (Hrm : (r mod two32 = r)%Z)
      by (apply Z.mod_small; clear - Hr'; unfold two32; lia).
    assert (Hp1m : ((p + 1) mod two32 = p + 1)%Z)
      by (apply Z.mod_small; clear - Hp2; lia).
    unfold horizon, two32 in Hc, Hp, He.
    (* 110fc beq s0, zero: not taken *)
    stepb step_beq_ft (FA F_110fc) D_110fc.
    { rewrite H8, getr_zero, <- sx32_zero, sx32_eqb, Hcm.
      apply Z.eqb_neq. exact Hc0. }
    (* 11100 bgeu s1, a0: not taken, the result is after the previous close *)
    stepb step_bgeu_ft (FA F_11100) D_11100.
    { rewrite H9, H10. fold e. rewrite sx32_ltu, Hpm, Hem.
      apply Z.ltb_lt. exact Hafter. }
    (* 11104 addiw s1, s1, 1 *)
    stepi (FA F_11104) D_11104. getr_resolve. imm_norm. rewrite R9.
    rewrite (v_addiw_sx32 _ p 1 (sx32_low p)).
    destruct (Z.eq_dec e (p + 1)) as [Hep | Hep].
    + (* 11108 beq a0, s1: taken, the result is the second after *)
      stepb step_beq_tk (FA F_11108) D_11108.
      { getr_resolve. rewrite R10. fold e. rewrite sx32_eqb, Hem, Hp1m.
        apply Z.eqb_eq. exact Hep. }
      apply epilogue. rewrite getr_other by reg_neq_tac. exact H2.
    + destruct Hbound as [Hbad | [Hmod Hnear]]; [contradiction |].
      (* 11108 beq a0, s1: not taken *)
      stepb step_beq_ft (FA F_11108) D_11108.
      { getr_resolve. rewrite R10. fold e. rewrite sx32_eqb, Hem, Hp1m.
        apply Z.eqb_neq. exact Hep. }
      (* 1110c remuw a1, a0, s2 *)
      stepi (FA F_1110c) D_1110c. getr_resolve. rewrite R10, R18. fold e.
      rewrite (v_remuw_sx32 _ _ e r (sx32_low e) (sx32_low r))
        by (rewrite Hrm; clear - Hr'; lia).
      rewrite Hem, Hrm, Hmod. clear Hmod.
      (* 11110 bne a1, zero: not taken, the result is on a boundary *)
      stepb step_bne_ft (FA F_11110) D_11110.
      { getr_resolve. rewrite <- sx32_zero, sx32_eqb. reflexivity. }
      (* 11114 srliw a1, s2, 1 *)
      stepi (FA F_11114) D_11114. getr_resolve. imm_norm. rewrite R18.
      rewrite (v_srliw1_sx32 _ r (sx32_low r)), Hrm.
      (* 11118 slli a0, a0, 32 *)
      stepi (FA F_11118) D_11118. getr_resolve. imm_norm. rewrite R10. fold e.
      (* 1111c slli a2, s0, 32 *)
      stepi (FA F_1111c) D_1111c. getr_resolve. imm_norm. rewrite R8.
      (* 11120 srli a0, a0, 32 *)
      stepi (FA F_11120) D_11120. getr_resolve. imm_norm.
      rewrite zext32_sx32, Hem.
      (* 11124 add a3, a1, a0 *)
      stepi (FA F_11124) D_11124. getr_resolve.
      rewrite v_add_lit by (clear - Hhalf He; lia).
      (* 11128 srli a2, a2, 32 *)
      stepi (FA F_11128) D_11128. getr_resolve. imm_norm.
      rewrite zext32_sx32, Hcm.
      (* 1112c bltu a3, a2: not taken, the result is not too early *)
      stepb step_bltu_ft (FA F_1112c) D_1112c.
      { getr_resolve. rewrite c_ltu_small by (clear - Hhalf He Hc; lia).
        apply Z.ltb_ge. clear - Hnear. lia. }
      (* 11130 add a1, a1, a2 *)
      stepi (FA F_11130) D_11130. getr_resolve.
      rewrite v_add_lit by (clear - Hhalf Hc; lia).
      (* 11134 bgeu a1, a0: taken, the result is not too late *)
      stepb step_bgeu_tk (FA F_11134) D_11134.
      { getr_resolve. rewrite c_ltu_small by (clear - Hhalf He Hc; lia).
        apply Z.ltb_ge. clear - Hnear. lia. }
      apply epilogue. getr_resolve. exact R2.
Qed.


(** ** The resolution table

    The image's segments are far below the stack, so the frame hides none of
    their bytes: a read there sees the image. *)
Lemma fmem_clear_low : mem_clear fmem 0x10000 0x12000.
Proof.
  pose proof Hlo as Hlo'. pose proof Hhi as Hhi'. unfold fmem.
  repeat (apply mem_clear_wbytes;
          [ | rewrite ?length_word_to_le_bytes, u_slot by lia; left; lia
            | rewrite ?length_word_to_le_bytes, u_slot by lia; lia ]).
  eapply mem_clear_wrap; [exact Hlaunch | unfold stack_max_size; lia].
Qed.

Lemma rdn_fmem_rodata : forall (a : word) n bs,
  (0x10000 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x12000)%Z ->
  rdn harness_segs (fun _ => None) a n = Some bs ->
  rdn segs fmem a n = Some bs.
Proof.
  intros a n bs Ha Hn H.
  transitivity (rdn segs (fun _ => None) a n).
  - apply rdn_ext; [lia |]. intros x Hx. apply fmem_clear_low. lia.
  - apply rdn_rom_app. exact H.
Qed.

(** 110d4-110e4: index [kLedgerPossibleTimeResolutions] and load the entry.
    One case per legal index; in each, every value is a literal. *)
Ltac table_case R :=
  eexists; exists R; split; [| split; [| split]];
  [ stepi (FA F_110d4) D_110d4; getr_resolve; imm_norm;
    match goal with H : reg_get _ 10 = _ |- _ => rewrite H end;
    stepi (FA F_110d8) D_110d8;
    stepi (FA F_110dc) D_110dc; getr_resolve; imm_norm;
    stepi (FA F_110e0) D_110e0; getr_resolve;
    chain_step;
      [ reflexivity
      | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 R))
                            (v := Z_to_bv 64 R);
        [ exact (FA F_110e4) | reflexivity | exact D_110e4
        | getr_resolve; imm_norm; wlits_closed;
          apply rdn_fmem_rodata;
          [ u_norm; lia | u_norm; cbn [Z.of_nat]; lia | vm_refl_bv ]
        | vm_compute; reflexivity ]
      | step_simpl ];
    apply mst_refl
  | cbv [resolutions In]; tauto
  | getr_resolve; vm_refl_bv
  | let y := fresh "y" in
    intros y ? ? ?; rewrite !getr_other by assumption; reflexivity ].

Lemma table_block : forall regs (i : Z),
  (0 <= i <= 5)%Z ->
  getr regs 10 = Z_to_bv 64 i ->
  exists regs' r,
    msteps segs (mkst regs 0x110d4 fmem rom) (mkst regs' 0x110e8 fmem rom)
    /\ In r resolutions
    /\ getr regs' 18 = sx32 r
    /\ (forall x : reg, x <> 10 -> x <> 11 -> x <> 18 ->
          getr regs' x = getr regs x).
Proof.
  intros regs i Hi H10.
  assert (R10 : reg_get regs 10 = Z_to_bv 64 i)
    by (rewrite <- H10; symmetry; apply getr_nz; reg_neq_tac).
  assert (Hcases : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5)%Z) by lia.
  clear Hi H10.
  destruct Hcases as [-> | [-> | [-> | [-> | [-> | ->]]]]].
  - table_case 10%Z.
  - table_case 20%Z.
  - table_case 30%Z.
  - table_case 60%Z.
  - table_case 90%Z.
  - table_case 120%Z.
Qed.


(** ** Reading the input

    From here on the program was started with exactly one argument. [arg]
    is that argument, any string of bytes the model allows; [P] is where
    the kernel put it. *)
Section OneArgument.

Hypothesis Hargc : length (in_argv inp) = 2%nat.

Local Abbreviation arg := (nth 1 (in_argv inp) []).
Local Abbreviation P :=
  (cat_argv_ptr (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp) 1).

Lemma P_bounds :
  (bv_unsigned sp <= bv_unsigned P)%Z
  /\ (bv_unsigned P + Z.of_nat (length arg) + 1 < 2^64)%Z.
Proof.
  apply (argv_ptr_bounds Sv48 inp mb sp brk rnd 1 Hlaunch). rewrite Hargc. lia.
Qed.

(** An argument has no zero byte in it: that is where it ends. *)
Lemma arg_no_nul : forall j, (j < length arg)%nat ->
  bv_unsigned (nth j arg (Z_to_bv 8 0)) <> 0%Z.
Proof.
  intros j Hj Hz.
  destruct Hva as (_ & _ & _ & Hnn & _).
  rewrite Forall_forall in Hnn.
  apply (Hnn arg); [apply nth_In; rewrite Hargc; lia |].
  replace (Z_to_bv 8 0) with (nth j arg (Z_to_bv 8 0));
    [apply nth_In; exact Hj |].
  apply bv_eq. rewrite Hz. reflexivity.
Qed.

(** Byte [j] of the argument, through the frame. Byte [length arg] is the
    terminating zero. *)
Lemma rdn_arg : forall j, (j <= length arg)%nat ->
  rdn segs fmem (P + nat_to_word j) 1
  = Some [nth j (arg ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)].
Proof.
  intros j Hj. destruct P_bounds as [Hp1 Hp2].
  pose proof (bv_unsigned_in_range _ P) as HP.
  assert (Hu : (bv_unsigned (P + nat_to_word j) = bv_unsigned P + Z.of_nat j)%Z).
  { rewrite word_add_nat. apply u_Z2bv; lia. }
  rewrite rdn_fmem_above by (rewrite Hu; lia).
  apply (read_argv_byte_k Sv48 segs inp mb harness_phdrs entry sp brk rnd 1 j Hlaunch);
    [rewrite Hargc; lia | exact Hj].
Qed.

Lemma ptr_succ : forall (q : word) j,
  v_addi (q + nat_to_word j) 1 = q + nat_to_word (S j).
Proof.
  intros q j. rewrite !word_add_nat. unfold v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned, bv_wrap_add_idemp_l. f_equal. lia.
Qed.

Lemma count_pred : forall k, (1 <= k <= 16)%Z ->
  v_addi (Z_to_bv 64 k) (-1) = Z_to_bv 64 (k - 1).
Proof.
  intros k Hk. unfold v_addi. rewrite u64_small by lia. reflexivity.
Qed.

Lemma reg_get_of_getr : forall regs (r : reg) v,
  r <> 0 -> getr regs r = v -> reg_get regs r = v.
Proof. intros regs r v Hr H. rewrite <- H. symmetry. apply getr_nz. exact Hr. Qed.

(** *** First loop: eight characters into s0 (11068-11084) *)

(** The argument ends here: the byte is zero and the test leaves. *)
Lemma loop1_stop : forall (j : nat) regs,
  j = length arg ->
  getr regs 2 = slot 32 ->
  getr regs 12 = P + nat_to_word j ->
  to_wexit segs (mkst regs 0x11068 fmem rom) [] (Z_to_bv 64 0).
Proof.
  intros j regs Hj H2 H12.
  assert (R12 := reg_get_of_getr regs 12 _ ltac:(reg_neq_tac) H12).
  assert (Hb : rdn segs fmem (P + nat_to_word j) 1 = Some [Z_to_bv 8 0]).
  { rewrite rdn_arg by lia. subst j.
    rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
  (* 11068 lbu a3, 0(a2) *)
  chain_step;
    [ reflexivity
    | eapply step_lbu with (b := Z_to_bv 8 0);
      [ exact (FA F_11068) | reflexivity | exact D_11068
      | getr_resolve; imm_norm; rewrite R12, v_addi_0; exact Hb ]
    | step_simpl ].
  (* 1106c beq a3, zero: taken *)
  stepb step_beq_tk (FA F_1106c) D_1106c.
  { getr_resolve. reflexivity. }
  apply epilogue. rewrite getr_other by reg_neq_tac. exact H2.
Qed.

(** One round, up to the loop's closing branch. *)
Lemma loop1_body : forall (j : nat) (k : Z) regs,
  (j < length arg)%nat -> (1 <= k <= 16)%Z ->
  getr regs 12 = P + nat_to_word j ->
  getr regs 11 = Z_to_bv 64 k ->
  exists regs',
    msteps segs (mkst regs 0x11068 fmem rom) (mkst regs' 0x11084 fmem rom)
    /\ getr regs' 12 = P + nat_to_word (S j)
    /\ getr regs' 11 = Z_to_bv 64 (k - 1)
    /\ (exists a, (0 <= a < two32)%Z /\ getr regs' 8 = sx32 a)
    /\ (forall x : reg, x <> 8 -> x <> 11 -> x <> 12 -> x <> 13 -> x <> 14 ->
          getr regs' x = getr regs x).
Proof.
  intros j k regs Hj Hk H12 H11.
  assert (R12 := reg_get_of_getr regs 12 _ ltac:(reg_neq_tac) H12).
  assert (R11 := reg_get_of_getr regs 11 _ ltac:(reg_neq_tac) H11).
  set (b := nth j arg (Z_to_bv 8 0)).
  assert (Hb : rdn segs fmem (P + nat_to_word j) 1 = Some [b]).
  { rewrite rdn_arg by lia. unfold b. rewrite app_nth1 by exact Hj. reflexivity. }
  assert (Hbnz : bv_unsigned b <> 0%Z) by (apply arg_no_nul; exact Hj).
  pose proof (bv_unsigned_in_range _ b) as Hbr.
  change (bv_modulus 8) with 256%Z in Hbr.
  destruct (nibble_acc (reg_get regs 8) b) as (a & Ha & Hacc).
  eexists. split; [| split; [| split; [| split]]].
  - (* 11068 lbu a3, 0(a2) *)
    chain_step;
      [ reflexivity
      | eapply step_lbu with (b := b);
        [ exact (FA F_11068) | reflexivity | exact D_11068
        | getr_resolve; imm_norm; rewrite R12, v_addi_0; exact Hb ]
      | step_simpl ].
    (* 1106c beq a3, zero: not taken *)
    stepb step_beq_ft (FA F_1106c) D_1106c.
    { getr_resolve. rewrite c_eq_small by lia. apply Z.eqb_neq. exact Hbnz. }
    (* 11070 slliw a4, s0, 4 *)
    stepi (FA F_11070) D_11070. getr_resolve. imm_norm.
    (* 11074 andi a3, a3, 15 *)
    stepi (FA F_11074) D_11074. getr_resolve. imm_norm.
    (* 11078 addi a1, a1, -1 *)
    stepi (FA F_11078) D_11078. getr_resolve. imm_norm. rewrite R11.
    (* 1107c or s0, a4, a3 *)
    stepi (FA F_1107c) D_1107c. getr_resolve.
    (* 11080 addi a2, a2, 1 *)
    stepi (FA F_11080) D_11080. getr_resolve. imm_norm. rewrite R12.
    apply mst_refl.
  - getr_resolve. apply ptr_succ.
  - getr_resolve. apply count_pred. exact Hk.
  - exists a. split; [exact Ha | getr_resolve; exact Hacc].
  - intros y Hy8 Hy11 Hy12 Hy13 Hy14.
    rewrite !getr_other by assumption. reflexivity.
Qed.

(** The whole loop. [K] is what comes after: if every state the loop can
    leave in goes on to exit 0, so does every state it can start in. *)
Lemma loop1 : forall (n j : nat) regs,
  (j + S n = 8)%nat -> (j <= length arg)%nat ->
  getr regs 2 = slot 32 ->
  getr regs 12 = P + nat_to_word j ->
  getr regs 11 = Z_to_bv 64 (Z.of_nat (S n)) ->
  (forall regs',
     (8 <= length arg)%nat ->
     (exists a, (0 <= a < two32)%Z /\ getr regs' 8 = sx32 a) ->
     (forall x : reg, x <> 8 -> x <> 11 -> x <> 12 -> x <> 13 -> x <> 14 ->
        getr regs' x = getr regs x) ->
     to_wexit segs (mkst regs' 0x11088 fmem rom) [] (Z_to_bv 64 0)) ->
  to_wexit segs (mkst regs 0x11068 fmem rom) [] (Z_to_bv 64 0).
Proof.
  induction n as [|n IH]; intros j regs Hjn Hj H2 H12 H11 K.
  - destruct (Nat.eq_dec j (length arg)) as [Hend | Hmore];
      [exact (loop1_stop j regs Hend H2 H12) |].
    destruct (loop1_body j 1 regs ltac:(lia) ltac:(lia) H12 H11)
      as (regs1 & Hm & _ & H11' & Hacc & Hfr).
    eapply msteps_to_wexit; [exact Hm |].
    (* 11084 bne a1, zero: not taken, the count has run out *)
    stepb step_bne_ft (FA F_11084) D_11084.
    { rewrite H11', getr_zero. reflexivity. }
    apply K; [lia | exact Hacc | exact Hfr].
  - destruct (Nat.eq_dec j (length arg)) as [Hend | Hmore];
      [exact (loop1_stop j regs Hend H2 H12) |].
    destruct (loop1_body j (Z.of_nat (S (S n))) regs ltac:(lia) ltac:(lia) H12 H11)
      as (regs1 & Hm & H12' & H11' & Hacc & Hfr).
    eapply msteps_to_wexit; [exact Hm |].
    (* 11084 bne a1, zero: taken, back to the top *)
    stepb step_bne_tk (FA F_11084) D_11084.
    { rewrite H11', getr_zero, c_eq_small by lia. apply Z.eqb_neq. lia. }
    apply (IH (S j) regs1);
      [ lia | lia
      | rewrite Hfr by reg_neq_tac; exact H2
      | exact H12'
      | rewrite H11'; f_equal; lia
      | ].
    intros regs2 Hlen Hacc2 Hfr2. apply K; [exact Hlen | exact Hacc2 |].
    intros x Hx8 Hx11 Hx12 Hx13 Hx14.
    rewrite Hfr2 by assumption. apply Hfr; assumption.
Qed.


(** *** Second loop: eight more characters into s1 (11094-110b0)

    The same loop with the registers swapped: the pointer is a1, the count
    a2, the accumulator s1. *)
Lemma loop2_stop : forall (j : nat) regs,
  j = length arg ->
  getr regs 2 = slot 32 ->
  getr regs 11 = P + nat_to_word j ->
  to_wexit segs (mkst regs 0x11094 fmem rom) [] (Z_to_bv 64 0).
Proof.
  intros j regs Hj H2 H11.
  assert (R11 := reg_get_of_getr regs 11 _ ltac:(reg_neq_tac) H11).
  assert (Hb : rdn segs fmem (P + nat_to_word j) 1 = Some [Z_to_bv 8 0]).
  { rewrite rdn_arg by lia. subst j.
    rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
  (* 11094 lbu a3, 0(a1) *)
  chain_step;
    [ reflexivity
    | eapply step_lbu with (b := Z_to_bv 8 0);
      [ exact (FA F_11094) | reflexivity | exact D_11094
      | getr_resolve; imm_norm; rewrite R11, v_addi_0; exact Hb ]
    | step_simpl ].
  (* 11098 beq a3, zero: taken *)
  stepb step_beq_tk (FA F_11098) D_11098.
  { getr_resolve. reflexivity. }
  apply epilogue. rewrite getr_other by reg_neq_tac. exact H2.
Qed.

Lemma loop2_body : forall (j : nat) (k : Z) regs,
  (j < length arg)%nat -> (1 <= k <= 16)%Z ->
  getr regs 11 = P + nat_to_word j ->
  getr regs 12 = Z_to_bv 64 k ->
  exists regs',
    msteps segs (mkst regs 0x11094 fmem rom) (mkst regs' 0x110b0 fmem rom)
    /\ getr regs' 11 = P + nat_to_word (S j)
    /\ getr regs' 12 = Z_to_bv 64 (k - 1)
    /\ (exists a, (0 <= a < two32)%Z /\ getr regs' 9 = sx32 a)
    /\ (forall x : reg, x <> 9 -> x <> 11 -> x <> 12 -> x <> 13 -> x <> 14 ->
          getr regs' x = getr regs x).
Proof.
  intros j k regs Hj Hk H11 H12.
  assert (R11 := reg_get_of_getr regs 11 _ ltac:(reg_neq_tac) H11).
  assert (R12 := reg_get_of_getr regs 12 _ ltac:(reg_neq_tac) H12).
  set (b := nth j arg (Z_to_bv 8 0)).
  assert (Hb : rdn segs fmem (P + nat_to_word j) 1 = Some [b]).
  { rewrite rdn_arg by lia. unfold b. rewrite app_nth1 by exact Hj. reflexivity. }
  assert (Hbnz : bv_unsigned b <> 0%Z) by (apply arg_no_nul; exact Hj).
  pose proof (bv_unsigned_in_range _ b) as Hbr.
  change (bv_modulus 8) with 256%Z in Hbr.
  destruct (nibble_acc (reg_get regs 9) b) as (a & Ha & Hacc).
  eexists. split; [| split; [| split; [| split]]].
  - (* 11094 lbu a3, 0(a1) *)
    chain_step;
      [ reflexivity
      | eapply step_lbu with (b := b);
        [ exact (FA F_11094) | reflexivity | exact D_11094
        | getr_resolve; imm_norm; rewrite R11, v_addi_0; exact Hb ]
      | step_simpl ].
    (* 11098 beq a3, zero: not taken *)
    stepb step_beq_ft (FA F_11098) D_11098.
    { getr_resolve. rewrite c_eq_small by lia. apply Z.eqb_neq. exact Hbnz. }
    (* 1109c slliw a4, s1, 4 *)
    stepi (FA F_1109c) D_1109c. getr_resolve. imm_norm.
    (* 110a0 andi a3, a3, 15 *)
    stepi (FA F_110a0) D_110a0. getr_resolve. imm_norm.
    (* 110a4 addi a2, a2, -1 *)
    stepi (FA F_110a4) D_110a4. getr_resolve. imm_norm. rewrite R12.
    (* 110a8 or s1, a4, a3 *)
    stepi (FA F_110a8) D_110a8. getr_resolve.
    (* 110ac addi a1, a1, 1 *)
    stepi (FA F_110ac) D_110ac. getr_resolve. imm_norm. rewrite R11.
    apply mst_refl.
  - getr_resolve. apply ptr_succ.
  - getr_resolve. apply count_pred. exact Hk.
  - exists a. split; [exact Ha | getr_resolve; exact Hacc].
  - intros y Hy9 Hy11 Hy12 Hy13 Hy14.
    rewrite !getr_other by assumption. reflexivity.
Qed.

Lemma loop2 : forall (n j : nat) regs,
  (j + S n = 16)%nat -> (j <= length arg)%nat ->
  getr regs 2 = slot 32 ->
  getr regs 11 = P + nat_to_word j ->
  getr regs 12 = Z_to_bv 64 (Z.of_nat (S n)) ->
  (forall regs',
     (16 <= length arg)%nat ->
     (exists a, (0 <= a < two32)%Z /\ getr regs' 9 = sx32 a) ->
     (forall x : reg, x <> 9 -> x <> 11 -> x <> 12 -> x <> 13 -> x <> 14 ->
        getr regs' x = getr regs x) ->
     to_wexit segs (mkst regs' 0x110b4 fmem rom) [] (Z_to_bv 64 0)) ->
  to_wexit segs (mkst regs 0x11094 fmem rom) [] (Z_to_bv 64 0).
Proof.
  induction n as [|n IH]; intros j regs Hjn Hj H2 H11 H12 K.
  - destruct (Nat.eq_dec j (length arg)) as [Hend | Hmore];
      [exact (loop2_stop j regs Hend H2 H11) |].
    destruct (loop2_body j 1 regs ltac:(lia) ltac:(lia) H11 H12)
      as (regs1 & Hm & _ & H12' & Hacc & Hfr).
    eapply msteps_to_wexit; [exact Hm |].
    (* 110b0 bne a2, zero: not taken *)
    stepb step_bne_ft (FA F_110b0) D_110b0.
    { rewrite H12', getr_zero. reflexivity. }
    apply K; [lia | exact Hacc | exact Hfr].
  - destruct (Nat.eq_dec j (length arg)) as [Hend | Hmore];
      [exact (loop2_stop j regs Hend H2 H11) |].
    destruct (loop2_body j (Z.of_nat (S (S n))) regs ltac:(lia) ltac:(lia) H11 H12)
      as (regs1 & Hm & H11' & H12' & Hacc & Hfr).
    eapply msteps_to_wexit; [exact Hm |].
    (* 110b0 bne a2, zero: taken *)
    stepb step_bne_tk (FA F_110b0) D_110b0.
    { rewrite H12', getr_zero, c_eq_small by lia. apply Z.eqb_neq. lia. }
    apply (IH (S j) regs1);
      [ lia | lia
      | rewrite Hfr by reg_neq_tac; exact H2
      | exact H11'
      | rewrite H12'; f_equal; lia
      | ].
    intros regs2 Hlen Hacc2 Hfr2. apply K; [exact Hlen | exact Hacc2 |].
    intros x Hx9 Hx11 Hx12 Hx13 Hx14.
    rewrite Hfr2 by assumption. apply Hfr; assumption.
Qed.

(** *** The last character, the range checks, and the call (110b4-110f8) *)
Lemma tail_block : forall regs (c p : Z),
  (16 <= length arg)%nat ->
  getr regs 2 = slot 32 -> getr regs 10 = P ->
  (0 <= c < two32)%Z -> getr regs 8 = sx32 c ->
  (0 <= p < two32)%Z -> getr regs 9 = sx32 p ->
  to_wexit segs (mkst regs 0x110b4 fmem rom) [] (Z_to_bv 64 0).
Proof.
  intros regs c p H16 H2 H10 Hc H8 Hp H9.
  assert (R2 := reg_get_of_getr regs 2 _ ltac:(reg_neq_tac) H2).
  assert (R10 := reg_get_of_getr regs 10 _ ltac:(reg_neq_tac) H10).
  assert (R8 := reg_get_of_getr regs 8 _ ltac:(reg_neq_tac) H8).
  assert (R9 := reg_get_of_getr regs 9 _ ltac:(reg_neq_tac) H9).
  set (b := nth 16 (arg ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)).
  assert (Hb : rdn segs fmem (v_addi P 16) 1 = Some [b]).
  { replace (v_addi P 16) with (P + nat_to_word 16)
      by (rewrite word_add_nat; reflexivity).
    apply rdn_arg. exact H16. }
  pose proof (bv_unsigned_in_range _ b) as Hbr.
  change (bv_modulus 8) with 256%Z in Hbr.
  unfold two32 in Hc, Hp.
  (* 110b4 lbu a0, 16(a0) *)
  chain_step;
    [ reflexivity
    | eapply step_lbu with (b := b);
      [ exact (FA F_110b4) | reflexivity | exact D_110b4
      | getr_resolve; imm_norm; rewrite R10; exact Hb ]
    | step_simpl ].
  destruct (Z.eq_dec (bv_unsigned b) 0) as [Hb0 | Hb0].
  { (* 110b8 beq a0, zero: taken, the argument is too short *)
    stepb step_beq_tk (FA F_110b8) D_110b8.
    { getr_resolve. rewrite c_eq_small by lia. apply Z.eqb_eq. exact Hb0. }
    apply epilogue. rewrite getr_other by reg_neq_tac. exact H2. }
  stepb step_beq_ft (FA F_110b8) D_110b8.
  { getr_resolve. rewrite c_eq_small by lia. apply Z.eqb_neq. exact Hb0. }
  (* 110bc andi a0, a0, 15 *)
  stepi (FA F_110bc) D_110bc. getr_resolve. imm_norm.
  set (i := Z.land (bv_unsigned b) 15).
  assert (Hi : (0 <= i < 16)%Z).
  { unfold i. change 15%Z with (Z.ones 4). rewrite Z.land_ones by lia.
    change (2 ^ 4)%Z with 16%Z. apply Z.mod_pos_bound. lia. }
  assert (Vi : v_andi (Z_to_bv 64 (bv_unsigned b)) 15 = Z_to_bv 64 i).
  { unfold v_andi. rewrite u64_small by lia. reflexivity. }
  rewrite Vi. clearbody i. clear Vi.
  (* 110c0 addi a1, zero, 5 *)
  stepiv (FA F_110c0) D_110c0 (Z_to_bv 64 5) ltac:(getr_resolve; imm_norm; bveq).
  destruct (Z.ltb_spec 5 i) as [Hbig | Hsmall].
  { (* 110c4 bltu a1, a0: taken, not a legal resolution index *)
    stepb step_bltu_tk (FA F_110c4) D_110c4.
    { getr_resolve. rewrite c_ltu_small by lia. apply Z.ltb_lt. exact Hbig. }
    apply epilogue. getr_resolve. exact R2. }
  stepb step_bltu_ft (FA F_110c4) D_110c4.
  { getr_resolve. rewrite c_ltu_small by lia. apply Z.ltb_ge. exact Hsmall. }
  (* 110c8 addi a1, zero, -61: the horizon, as a 32-bit value *)
  stepiv (FA F_110c8) D_110c8 (sx32 4294967235)
    ltac:(getr_resolve; imm_norm; vm_refl_bv).
  destruct (Z.ltb_spec 4294967235 c) as [Hcbig | Hcok].
  { (* 110cc bltu a1, s0: taken, the close time is past the horizon *)
    stepb step_bltu_tk (FA F_110cc) D_110cc.
    { getr_resolve. rewrite R8, sx32_ltu. unfold two32.
      rewrite !Z.mod_small by lia. apply Z.ltb_lt. exact Hcbig. }
    apply epilogue. getr_resolve. exact R2. }
  stepb step_bltu_ft (FA F_110cc) D_110cc.
  { getr_resolve. rewrite R8, sx32_ltu. unfold two32.
    rewrite !Z.mod_small by lia. apply Z.ltb_ge. exact Hcok. }
  destruct (Z.ltb_spec 4294967235 p) as [Hpbig | Hpok].
  { (* 110d0 bltu a1, s1: taken, the previous close is past the horizon *)
    stepb step_bltu_tk (FA F_110d0) D_110d0.
    { getr_resolve. rewrite R9, sx32_ltu. unfold two32.
      rewrite !Z.mod_small by lia. apply Z.ltb_lt. exact Hpbig. }
    apply epilogue. getr_resolve. exact R2. }
  stepb step_bltu_ft (FA F_110d0) D_110d0.
  { getr_resolve. rewrite R9, sx32_ltu. unfold two32.
    rewrite !Z.mod_small by lia. apply Z.ltb_ge. exact Hpok. }
  (* 110d4-110e4: load the resolution *)
  match goal with |- to_wexit _ (mkst ?R _ _ _) _ _ =>
    destruct (table_block R i ltac:(lia) ltac:(getr_resolve; reflexivity))
      as (regs1 & r & Hm & Hr & H18 & Hfr)
  end.
  eapply msteps_to_wexit; [exact Hm |]. clear Hm.
  assert (G2 : reg_get regs1 2 = slot 32).
  { apply reg_get_of_getr; [reg_neq_tac |].
    rewrite Hfr by reg_neq_tac. getr_resolve. exact R2. }
  assert (G8 : reg_get regs1 8 = sx32 c).
  { apply reg_get_of_getr; [reg_neq_tac |].
    rewrite Hfr by reg_neq_tac. getr_resolve. exact R8. }
  assert (G9 : reg_get regs1 9 = sx32 p).
  { apply reg_get_of_getr; [reg_neq_tac |].
    rewrite Hfr by reg_neq_tac. getr_resolve. exact R9. }
  assert (G18 := reg_get_of_getr regs1 18 _ ltac:(reg_neq_tac) H18).
  (* 110e8 addi a0, s0, 0 *)
  stepiv (FA F_110e8) D_110e8 (sx32 c)
    ltac:(getr_resolve; imm_norm; rewrite G8; apply v_addi_0).
  (* 110ec addi a1, s2, 0 *)
  stepiv (FA F_110ec) D_110ec (sx32 r)
    ltac:(getr_resolve; imm_norm; rewrite G18; apply v_addi_0).
  (* 110f0 addi a2, s1, 0 *)
  stepiv (FA F_110f0) D_110f0 (sx32 p)
    ltac:(getr_resolve; imm_norm; rewrite G9; apply v_addi_0).
  (* 110f4 auipc ra, 0 *)
  stepi (FA F_110f4) D_110f4.
  (* 110f8 jalr ra, -220(ra): call eff_close_time *)
  stepjr (FA F_110f8) D_110f8 (Z_to_bv 64 0x110f4) ltac:(getr_resolve; bveq).
  (* 11018-11038: the code under test *)
  assert (Hr' : (0 < r < two32)%Z)
    by (clear - Hr; unfold two32; legal_resolution Hr; lia).
  match goal with |- to_wexit _ (mkst ?R _ _ _) _ _ =>
    destruct (eff_close_time_code vt R fmem rom c r p (Z_to_bv 64 0x110fc)
                ltac:(unfold two32; lia) Hr' ltac:(unfold two32; lia)
                ltac:(getr_resolve; reflexivity)
                ltac:(getr_resolve; reflexivity)
                ltac:(getr_resolve; reflexivity)
                ltac:(getr_resolve; vm_refl_bv))
      as (regs2 & Hm2 & Ha0 & Hfr2)
  end.
  eapply msteps_to_wexit; [exact Hm2 |]. clear Hm2. norm_pc.
  (* 110fc-11140: the checks *)
  apply (check_block regs2 c r p Hr);
    [ unfold horizon, two32; lia
    | unfold horizon, two32; lia
    | rewrite Hfr2 by reg_neq_tac; getr_resolve; exact G2
    | rewrite Hfr2 by reg_neq_tac; getr_resolve; exact G8
    | rewrite Hfr2 by reg_neq_tac; getr_resolve; exact G9
    | rewrite Hfr2 by reg_neq_tac; getr_resolve; exact G18
    | exact Ha0 ].
Qed.


(** The pointer to the argument, where [_start] left it: [argv[1]] is the
    third word of the initial stack. *)
Lemma rdn_argv1 :
  rdn segs fmem (v_addi (v_addi sp 8) 8) 8 = Some (word_le8 P).
Proof.
  pose proof Hlo as Hlo'. pose proof Hhi as Hhi'.
  replace (v_addi (v_addi sp 8) 8) with (sp + nat_to_word (8 + 8 * 1)).
  2:{ rewrite word_add_nat. unfold v_addi. rewrite u_Z2bv by lia.
      f_equal. cbn [Nat.add Nat.mul Z.of_nat]. lia. }
  rewrite rdn_fmem_above
    by (rewrite word_add_nat, u_Z2bv by (cbn [Nat.add Nat.mul]; lia);
        cbn [Nat.add Nat.mul]; lia).
  apply read_argv_ptr_k; [rewrite Hargc; lia |].
  exact (bsb_nw Sv48 inp mb harness_phdrs entry sp brk rnd Hvl Hlaunch Hsp_hi).
Qed.

End OneArgument.
End Frame.

(** ** From the first instruction

    [_start], then [main] up to its first loop. After [main] has saved its
    four words, memory is [fmem] and stays that way. *)
Local Abbreviation P1 :=
  (cat_argv_ptr (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp) 1).

Ltac slot_bounds :=
  rewrite u_slot by lia; unfold stack_window_reach, stack_max_size;
  cbn [Z.of_nat]; lia.

Ltac frame_store_ok :=
  apply (store_ok_mono segs 8 M0);
  [ repeat first [ apply wbytes_grows
                 | eapply mem_grows_trans; [ | apply wbytes_grows ] ]
  | apply (store_ok_wrap_window_valid segs inp mb harness_phdrs entry sp brk
             _ 8 rnd Hvl Hlaunch); slot_bounds ].

Lemma main_wexit :
  to_wexit segs
    (mkst (regupd (regupd bvmap_empty 10 (Z_to_bv 64 0)) 2 sp) 0x11000 M0 rom)
    [] (Z_to_bv 64 0).
Proof.
  pose proof Hlo as Hlo'. pose proof Hhi as Hhi'.
  (* 11000 ld a0, 0(sp): argc *)
  chain_step;
    [ reflexivity
    | eapply step_ld with (bs := word_le8 (argcN inp)) (v := argcN inp);
      [ exact (FA F_11000) | reflexivity | exact D_11000
      | getr_resolve; imm_norm; rewrite v_addi_0;
        rewrite rdn_wrap_stack_above by (u_norm; lia);
        apply read_argc;
        exact (bsb_nw Sv48 inp mb harness_phdrs entry sp brk rnd Hvl Hlaunch Hsp_hi)
      | apply bytes_le_n_to_le_8 ]
    | step_simpl ].
  (* 11004 addi a1, sp, 8: argv *)
  stepi (FA F_11004) D_11004. getr_resolve. imm_norm.
  (* 11008 auipc ra, 0 *)
  stepi (FA F_11008) D_11008.
  (* 1100c jalr ra, 52(ra): call main *)
  stepjr (FA F_1100c) D_1100c (Z_to_bv 64 0x11008) ltac:(getr_resolve; bveq).
  (* 1103c addi sp, sp, -32 *)
  stepiv (FA F_1103c) D_1103c (slot 32)
    ltac:(getr_resolve; imm_norm; unfold slot, v_addi; f_equal; lia).
  (* 11040 sd ra, 24(sp) *)
  chain_step;
    [ reflexivity
    | eapply step_sd_at with (a := slot 8) (v := ret_start);
      [ exact (FA F_11040) | reflexivity | exact D_11040
      | getr_resolve; imm_norm; apply slot_addi; lia
      | getr_resolve; vm_refl_bv
      | apply (store_ok_wrap_window_valid segs inp mb harness_phdrs entry sp brk
                 _ 8 rnd Hvl Hlaunch); slot_bounds ]
    | step_simpl ].
  (* 11044 sd s0, 16(sp) *)
  chain_step;
    [ reflexivity
    | eapply step_sd_at with (a := slot 16);
      [ exact (FA F_11044) | reflexivity | exact D_11044
      | getr_resolve; imm_norm; apply slot_addi; lia
      | getr_resolve; reflexivity
      | frame_store_ok ]
    | step_simpl ].
  (* 11048 sd s1, 8(sp) *)
  chain_step;
    [ reflexivity
    | eapply step_sd_at with (a := slot 24);
      [ exact (FA F_11048) | reflexivity | exact D_11048
      | getr_resolve; imm_norm; apply slot_addi; lia
      | getr_resolve; reflexivity
      | frame_store_ok ]
    | step_simpl ].
  (* 1104c sd s2, 0(sp) *)
  chain_step;
    [ reflexivity
    | eapply step_sd_at with (a := slot 32);
      [ exact (FA F_1104c) | reflexivity | exact D_1104c
      | getr_resolve; imm_norm; apply slot_addi; lia
      | getr_resolve; reflexivity
      | frame_store_ok ]
    | step_simpl ].
  (* the frame is built: name the memory *)
  lazymatch goal with
  | |- to_wexit ?s
         (mkst ?R ?pc
            (wbytes (wbytes (wbytes (wbytes _ _ _) _ (word_to_le_bytes 8 ?x8))
                            _ (word_to_le_bytes 8 ?x9))
                    _ (word_to_le_bytes 8 ?x18)) ?ro) ?b ?c =>
      change (to_wexit s (mkst R pc (fmem x8 x9 x18) ro) b c)
  end.
  (* 11050 addi a2, zero, 2 *)
  stepiv (FA F_11050) D_11050 (Z_to_bv 64 2) ltac:(getr_resolve; imm_norm; bveq).
  pose proof (valid_argv_len (in_argv inp) Hva) as Hargmax.
  destruct (Nat.eq_dec (length (in_argv inp)) 2) as [Hargc | Hargc].
  2:{ (* 11054 bne a0, a2: taken, not exactly one argument *)
      stepb step_bne_tk (FA F_11054) D_11054.
      { getr_resolve. unfold c_eq, bv_eqb.
        rewrite (u_argcN inp Hva), u64_small by lia. apply Z.eqb_neq. lia. }
      apply epilogue. getr_resolve. reflexivity. }
  stepb step_bne_ft (FA F_11054) D_11054.
  { getr_resolve. unfold c_eq, bv_eqb.
    rewrite (u_argcN inp Hva), Hargc. reflexivity. }
  (* 11058 addi s0, zero, 0 *)
  stepi (FA F_11058) D_11058.
  (* 1105c ld a0, 8(a1): argv[1] *)
  chain_step;
    [ reflexivity
    | eapply step_ld with (bs := word_le8 P1) (v := P1);
      [ exact (FA F_1105c) | reflexivity | exact D_1105c
      | getr_resolve; imm_norm; apply rdn_argv1; exact Hargc
      | apply bytes_le_n_to_le_8 ]
    | step_simpl ].
  (* 11060 addi a1, zero, 8 *)
  stepiv (FA F_11060) D_11060 (Z_to_bv 64 8) ltac:(getr_resolve; imm_norm; bveq).
  (* 11064 addi a2, a0, 0 *)
  stepiv (FA F_11064) D_11064 constr:(P1) ltac:(getr_resolve; imm_norm; apply v_addi_0).
  (* 11068-11084: the first eight characters *)
  apply (loop1 _ _ _ Hargc 7 0);
    [ lia | lia
    | getr_resolve; reflexivity
    | getr_resolve; symmetry; apply word_add_nat_0
    | getr_resolve; reflexivity
    | ].
  intros regs1 Hlen8 (c & Hc & Hacc1) Hfr1.
  assert (G2 : reg_get regs1 2 = slot 32).
  { apply reg_get_of_getr; [reg_neq_tac |].
    rewrite Hfr1 by reg_neq_tac. getr_resolve. reflexivity. }
  assert (G10 : reg_get regs1 10 = P1).
  { apply reg_get_of_getr; [reg_neq_tac |].
    rewrite Hfr1 by reg_neq_tac. getr_resolve. reflexivity. }
  assert (G8 := reg_get_of_getr regs1 8 _ ltac:(reg_neq_tac) Hacc1).
  (* 11088 addi s1, zero, 0 *)
  stepi (FA F_11088) D_11088.
  (* 1108c addi a1, a0, 8 *)
  stepiv (FA F_1108c) D_1108c constr:(P1 + nat_to_word 8)
    ltac:(getr_resolve; imm_norm; rewrite G10, word_add_nat; reflexivity).
  (* 11090 addi a2, zero, 8 *)
  stepiv (FA F_11090) D_11090 (Z_to_bv 64 8) ltac:(getr_resolve; imm_norm; bveq).
  (* 11094-110b0: the next eight *)
  apply (loop2 _ _ _ Hargc 7 8);
    [ lia | exact Hlen8
    | getr_resolve; exact G2
    | getr_resolve; reflexivity
    | getr_resolve; reflexivity
    | ].
  intros regs2 Hlen16 (p & Hp & Hacc2) Hfr2.
  (* 110b4 on: the last character, the checks, the call *)
  apply (tail_block _ _ _ Hargc regs2 c p Hlen16);
    [ rewrite Hfr2 by reg_neq_tac; getr_resolve; exact G2
    | rewrite Hfr2 by reg_neq_tac; getr_resolve; exact G10
    | exact Hc
    | rewrite Hfr2 by reg_neq_tac; getr_resolve; exact G8
    | exact Hp
    | exact Hacc2 ].
Qed.

End Run.

(* ========================================================================= *)
(** * The theorem

    For every valid launch of this binary - every argument list, every
    environment, every placement of the stack - every execution ends by
    calling exit with status 0. It does not trap, fault, loop forever or
    step outside the model. In particular it never reaches the trap at
    0x11138, which is where a failed check of the close-time code goes.

    [halts_allowed_T] is the model's own statement
    (EquivalenceDefinition/HaltsAllowed.v), not one written here. *)
Theorem harness_halts :
  halts_allowed_T [Z_to_bv 64 0]
    (mkImage Harness.loaded_segments Harness.init_pc Harness.phdrs).
Proof.
  apply halts_allowed_T_of_must_exit_with with (code := Z_to_bv 64 0);
    [| left; reflexivity].
  intros [sp brk mb rnd] inp Hen Hvalid.
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct Hen as (Hsp & _ & _ & _ & Hlaunch).
  destruct Hsp as (Hsp_lo & Hsp_hi & _).
  red in Hvalid.
  repeat (lazymatch type of Hvalid with
          | _ /\ _ => let Hc := fresh "Hc" in destruct Hvalid as [Hc Hvalid]
          end).
  apply (cat_must_exit_with_te harness_segs HarnessMemImage_init_pc
           HarnessMemImage_phdrs sp brk mb rnd source_alloc_limit inp []
           (Z_to_bv 64 0)).
  - rewrite init_mkst. norm_pc. apply main_wexit with (brk := brk); assumption.
  - (* the program writes nothing *)
    constructor.
  - left. reflexivity.
Qed.
