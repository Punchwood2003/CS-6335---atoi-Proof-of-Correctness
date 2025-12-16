(* Digit parsing and value computation for atoi *)

(* Import standard libraries *)
Require Import ZArith.
Require Import Lia.

(* Import Picinae notations/tactics *)
Require Import Picinae_armv8_pcode.
Import ARM8Notations.

Open Scope N.
  
(* ascii values as decimal nums (not hex) *)
Definition digit (n:N) : bool :=
  (48 <=? n) && (n <=? 57).
  
Open Scope N. 
(* Fixpoint that accumulates digit values up to k bytes *)
Fixpoint handle_digits (mem:memory) (p:addr) (k:nat) (val:nat) :=
  match k with
  | O => O
  | S k' =>
    if digit (mem Ⓑ[p]) then
        handle_digits mem (p + 1) k'
          (val * 10 + N.to_nat (mem Ⓑ[p]) - 48)
      else
        val
  end.

(* A byte represents a decimal digit (ASCII '0'-'9': 0x30-0x39) *)
Definition is_digit (b : N) : Prop :=
  0x30 <= b /\ b <= 0x39.

(* Boolean version for decidability *)
Definition is_digit_b (b : N) : bool :=
  (0x30 <=? b) && (b <=? 0x39).

(* Decidability lemma for is_digit *)
Lemma is_digit_dec : forall b, {is_digit b} + {~is_digit b}.
Proof.
  intro b.
  destruct (is_digit_b b) eqn:Hb.
  - left. unfold is_digit, is_digit_b in *.
    apply Bool.andb_true_iff in Hb. destruct Hb as [H1 H2].
    apply N.leb_le in H1. apply N.leb_le in H2. split; assumption.
  - right. unfold is_digit, is_digit_b in *.
    apply Bool.andb_false_iff in Hb.
    intros [H1 H2]. destruct Hb as [Hb|Hb]; 
    [apply N.leb_gt in Hb; lia | apply N.leb_gt in Hb; lia].
Qed.

(* Convert ASCII digit to numeric value *)
Definition digit_value (b : N) : N :=
  b - 0x30.
