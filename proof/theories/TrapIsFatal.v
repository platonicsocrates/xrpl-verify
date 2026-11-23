(** * The trap is fatal in the model

    A failed check in the test jumps to 0x11138, where the compiler put
    [unimp]. The model decodes that word as a write to the read-only [cycle]
    counter, which RISC-V defines as an illegal instruction.

    The halting theorem does not mention this address: its proof walks every
    execution and none of them goes there. This lemma is what makes the
    theorem say something about the checks. In the model, a process that
    reaches 0x11138 faults on the spot, and a process that faults does not
    exit with status 0. So "always exits with status 0" implies "no check
    ever fails". Without this lemma that step would rest on reading the
    disassembly. *)

From Stdlib Require Import NArith ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Common Require Import PropExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From XrplVerify Require Import HarnessMemImage HarnessCode SegsApp.
Import ListNotations.
Open Scope bv_scope.

(** [csrrw] to a read-only CSR is a fault, whatever the machine state. *)
Lemma step_csrrw_read_only :
  forall {fx : FPState} segs regs pc mem rom w rd rs1 csr,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Csr CSR_RW rd rs1 csr, 4%Z) ->
  csr_read_only csr = true ->
  RiscvSemantics.step segs (mkst regs pc mem rom) = MachineFault.
Proof.
  intros fx segs regs pc mem rom w rd rs1 csr Hf He Hd Hro.
  step_pipeline Hf He Hd.
  unfold csr_write_illegal. rewrite Hro. reflexivity.
Qed.

(** At 0x11138 the machine faults: from every register state and every
    memory, and whatever segments follow the image's own. *)
Theorem trap_is_fatal : forall {fx : FPState} vt regs mem rom,
  RiscvSemantics.step (harness_segs ++ vt) (mkst regs 0x11138 mem rom)
  = MachineFault.
Proof.
  intros fx vt regs mem rom.
  exact (step_csrrw_read_only _ _ _ _ _ _ _ _ _
           (fetch_word_app harness_segs vt _ _ F_11138) eq_refl D_11138 eq_refl).
Qed.
