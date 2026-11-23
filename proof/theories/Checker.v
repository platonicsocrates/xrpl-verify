(** * The check

    This file proves nothing. It pins what was proved to the statement the
    model publishes, the way Theorem's own checker does for its examples
    (tools/gen_checker.py in rocq-linux-process-semantics):

    1. [Checked] ascribes the theorem to [HaltsAllowed.SPEC_HALTS_ALLOWED],
       so it has exactly the model's type: for the memory image of the test
       binary, with exit status 0 as the only status allowed.
    2. [ImageWf] ascribes the image to [Equivalence.IMAGE_WF]: the image can
       start. Without it the theorem could be true because no valid launch
       exists.
    3. [Print Assumptions] lists every axiom the proofs rest on.

    tools/check.sh builds this file and compares that list with
    allowed-axioms.txt. *)

From Stdlib Require Import List ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence HaltsAllowed.
From XrplVerify Require HarnessMemImage CloseTimeSpec CloseTimeCode TrapIsFatal HarnessHalts.
Import ListNotations.

(** The only exit status the statement allows. *)
Module ExitZero <: HaltsAllowed.ALLOWED_EXITS.
  Definition codes : list word := [Z_to_bv 64 0].
End ExitZero.

Module Checked <: HaltsAllowed.SPEC_HALTS_ALLOWED ExitZero HarnessMemImage.Harness.
  Definition halts_allowed := HarnessHalts.harness_halts.
End Checked.

Module ImageWf <: Equivalence.IMAGE_WF HarnessMemImage.Harness.
  Lemma entry_fetchable :
    Equivalence.image_entry_fetchable
      HarnessMemImage.Harness.loaded_segments HarnessMemImage.Harness.init_pc = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma phdrs_readable :
    Equivalence.image_phdrs_readable
      HarnessMemImage.Harness.loaded_segments HarnessMemImage.Harness.phdrs = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma brk_satisfiable :
    Equivalence.image_brk_satisfiable
      HarnessMemImage.Harness.loaded_segments = true.
  Proof. vm_compute. reflexivity. Qed.
End ImageWf.

Goal True.
  idtac "<halts_allowed>".
  Print Assumptions Checked.halts_allowed.
  idtac "</halts_allowed>".
  idtac "<eff_close_time_code>".
  Print Assumptions CloseTimeCode.eff_close_time_code.
  idtac "</eff_close_time_code>".
  idtac "<trap_is_fatal>".
  Print Assumptions TrapIsFatal.trap_is_fatal.
  idtac "</trap_is_fatal>".
  idtac "<spec>".
  Print Assumptions CloseTimeSpec.eff_after_prior.
  Print Assumptions CloseTimeSpec.eff_on_boundary.
  Print Assumptions CloseTimeSpec.round_nearest.
  Print Assumptions CloseTimeSpec.eff_zero.
  Print Assumptions CloseTimeSpec.eff_range.
  Print Assumptions CloseTimeSpec.round_wraps_past_horizon.
  Print Assumptions CloseTimeSpec.round_wraps_just_past_horizon.
  Print Assumptions CloseTimeSpec.eff_not_after_prior_at_the_end.
  idtac "</spec>".
Abort.
