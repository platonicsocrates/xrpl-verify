(** * Facts about the image survive a longer segment list

    A run does not read the image's own segment list. It reads that list
    followed by the kernel's vDSO pair ([Run.run_segments]). The generated
    fetch facts are about the image's own list. Every reader scans the list
    from the head, so a hit among the image's segments is the same hit in any
    longer list. Proof-side file, after the same lemmas in Theorem's example
    (theories/Examples/rwx_flag_ns/rwx_flag_ns_defs.v, MIT licence). *)

From Stdlib Require Import NArith ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Common Require Import PropExec.
Import ListNotations.
Open Scope bv_scope.

Lemma find_segment_app : forall segs vt a n seg,
  find_segment segs a n = Some seg -> find_segment (segs ++ vt) a n = Some seg.
Proof.
  induction segs as [|s rest IH]; intros vt a n seg H; [discriminate|].
  cbn [find_segment app] in *.
  match goal with |- (if ?c then _ else _) = _ => destruct c end;
    [exact H | exact (IH vt a n seg H)].
Qed.

Lemma code_read_app : forall segs vt (a : word) n bs,
  code_read segs a n = Some bs -> code_read (segs ++ vt) a n = Some bs.
Proof.
  intros segs vt a n bs H. unfold code_read in *.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hf;
    [|discriminate].
  rewrite (find_segment_app segs vt _ _ seg Hf). exact H.
Qed.

Lemma fetch_word_app : forall segs vt (pc : word) w,
  fetch_word segs pc = Some w -> fetch_word (segs ++ vt) pc = Some w.
Proof.
  intros segs vt pc w H. unfold fetch_word in *.
  destruct (negb (Z.eqb (bv_unsigned pc mod 2) 0)%Z); [discriminate|].
  destruct (code_read segs pc 4) as [bs|] eqn:Hc; [|discriminate].
  rewrite (code_read_app segs vt pc 4 bs Hc). exact H.
Qed.

(** Read-only data: a byte of the image read through an empty overlay. *)
Lemma memory_read_app : forall segs vt (a : word) n bs,
  memory_read segs a n = Some bs -> memory_read (segs ++ vt) a n = Some bs.
Proof.
  intros segs vt a n bs H. unfold memory_read in *.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [seg|] eqn:Hf;
    [|discriminate].
  rewrite (find_segment_app segs vt _ _ seg Hf). exact H.
Qed.

Lemma seg_rom_app : forall segs vt (a : word) b,
  seg_rom segs a = Some b -> seg_rom (segs ++ vt) a = Some b.
Proof.
  intros segs vt a b H. unfold seg_rom in *.
  destruct (memory_read segs a 1) as [bs|] eqn:Hm; [|discriminate].
  rewrite (memory_read_app segs vt a 1 bs Hm). exact H.
Qed.

Lemma rdn_rom_app : forall segs vt n (a : word) bs,
  rdn segs (fun _ => None) a n = Some bs ->
  rdn (segs ++ vt) (fun _ => None) a n = Some bs.
Proof.
  intros segs vt n. induction n as [|n IH]; intros a bs H; [exact H|].
  cbn [rdn] in *.
  destruct (seg_rom segs a) as [b|] eqn:Hb; [|discriminate].
  rewrite (seg_rom_app segs vt a b Hb).
  destruct (rdn segs (fun _ => None) (a + 1) n) as [rest|] eqn:Hr; [|discriminate].
  rewrite (IH (a + 1) rest Hr). exact H.
Qed.
