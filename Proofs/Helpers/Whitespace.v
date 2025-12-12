(* Whitespace detection and skipping logic for atoi *)

Require Import Picinae_armv8_pcode.
Require Import Utf8.
Require Import NArith.
Require Import ZArith.
Require Import Lia.
Import ARM8Notations.

Open Scope N.

(* A byte is whitespace: 0x09-0x0d (tab through carriage return) or 0x20 (space) *)
Definition is_whitespace (b : N) : Prop :=
  (0x09 <= b /\ b <= 0x0d) \/ b = 0x20.

(* Boolean version for decidability *)
Definition is_whitespace_b (b : N) : bool :=
  ((0x09 <=? b) && (b <=? 0x0d)) || (b =? 0x20).

(* Decidability lemma for is_whitespace *)
Lemma is_whitespace_dec : forall b, {is_whitespace b} + {~is_whitespace b}.
Proof.
  intro b.
  destruct (is_whitespace_b b) eqn:Hb.
  - left. unfold is_whitespace, is_whitespace_b in *.
    apply Bool.orb_true_iff in Hb. destruct Hb as [Hb|Hb].
    + left. apply Bool.andb_true_iff in Hb. destruct Hb as [H1 H2].
      apply N.leb_le in H1. apply N.leb_le in H2. split; assumption.
    + right. apply N.eqb_eq in Hb. assumption.
  - right. unfold is_whitespace, is_whitespace_b in *.
    apply Bool.orb_false_iff in Hb. destruct Hb as [Hb1 Hb2].
    intros [H|H].
    + destruct H as [H1 H2]. apply Bool.andb_false_iff in Hb1.
      destruct Hb1 as [Hb1|Hb1]; [apply N.leb_gt in Hb1; lia | apply N.leb_gt in Hb1; lia].
    + apply N.eqb_neq in Hb2. contradiction.
Qed.

(* Fixpoint that skips whitespace characters up to k bytes *)
Fixpoint handle_whitespace (mem:memory) (p:addr) (k:nat) : addr :=
  match k with
  | O => p (* no more budget, return current position *)
  | S k' => 
    if is_whitespace_dec (mem Ⓑ[p])
    then handle_whitespace mem (p ⊕ 1) k' (* skip whitespace, continue *)
    else p (* found non-whitespace, stop *)
  end.