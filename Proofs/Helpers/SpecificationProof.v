Require Import ZArith.
Require Import Lia.

Require Import Whitespace.
Require Import Sign.
Require Import Digits.
Require Import Specification.

Require Import Picinae_armv8_pcode.
Import ARM8Notations.

(* === prove that whitespace works === *) 
Close Scope Z.
Theorem whitespace_handler_correct: 
forall (mem:memory) (p:addr) (w:nat), 
  p <= handle_whitespace mem p w <= p+(N.of_nat w). 
  
Proof. 
  intros. revert p. induction w.
    intros. simpl. rewrite N.add_0_r. split; apply N.le_refl.
    intros. simpl. specialize (IHw (p+1)). split; lia.
Qed.

(* === prove that sign handling works === *) 
(* the pointer doesnt move if theres no sign *) 
Theorem sign_point_no_sign:
  forall (mem:memory) (p:addr),
    (Z.of_N (mem Ⓑ[ p ]) <> Z.of_N 43) /\
    (Z.of_N (mem Ⓑ[ p ]) <> Z.of_N 45)
    -> handle_sign_space mem p = p.
Proof. 
  intros. unfold handle_sign_space. destruct H as [H43 H45]. 
  set (x := Z.of_N (mem Ⓑ[p])).
    destruct (Z.eq_dec x 45) as [Hx45 | Hx45].
      exfalso. apply H45. assumption.
    destruct (Z.eq_dec x 43) as [Hx43 | Hx43].
      exfalso. apply H43. assumption.
    reflexivity.
Qed.

(* the pointer moves one space if theres a sign *)
Theorem sign_point_has_sign:
  forall (mem:memory) (p:addr),
    (Z.of_N (mem Ⓑ[ p ]) = Z.of_N 43) \/
    (Z.of_N (mem Ⓑ[ p ]) = Z.of_N 45)
    -> handle_sign_space mem p = p+1.
Proof.
  intros. unfold handle_sign_space.
  set (x := Z.of_N (mem Ⓑ[p])).
    destruct H as [Hx43 | Hx45].
    (* x = 43 *) 
      destruct (Z.eq_dec x 45).
      simpl. reflexivity.    
      destruct (Z.eq_dec x 43).
        simpl. reflexivity.
        contradiction.
    (* x = 45 *)
      destruct (Z.eq_dec x 45).
        simpl. reflexivity.
        contradiction.  
Qed.

Open Scope Z.
(* sign value is either +1 or -1 *) 
Theorem sign_value_correct: 
  forall (mem:memory) (p:addr), 
    handle_sign mem p = 1 \/ handle_sign mem p = -1.
Proof. 
  intros. unfold handle_sign. destruct (Z.eq_dec (Z.of_N (mem Ⓑ[ p ])) 45); auto.
Qed.

Theorem sign_value_neg:
  forall (mem:memory) (p:addr),
    (Z.of_N (mem Ⓑ[ p ]) = Z.of_N 45) -> handle_sign mem p = -1.
Proof.
  intros. unfold handle_sign. destruct (Z.eq_dec (Z.of_N (mem Ⓑ[ p ])) 45).
    reflexivity. contradiction.
Qed.

(* positive sign value *)
Theorem sign_value_pos:
  forall (mem:memory) (p:addr),
    (Z.of_N (mem Ⓑ[ p ]) <> Z.of_N 45) -> handle_sign mem p = 1.
Proof.
  intros. unfold handle_sign. destruct (Z.eq_dec (Z.of_N (mem Ⓑ[ p ])) 45).
  contradiction. reflexivity.  
Qed.


(* === prove that digits read properly === *) 
(* returns some number *) 
Theorem digit_handler_correct: 
  forall (mem:memory) (p:addr) (k:nat), 
    Z.of_nat (handle_digits mem p k 0) >= 0. 
Proof.
  intros. induction k; lia.
Qed.

(* === prove that parser works === *) 
(* our number is either 0, a positive, or a negative *)
Theorem atoi_sign_correct :
  forall mem p w d,
    let z := atoi mem p w d in
    z = 0 \/
    z = Z.of_nat (handle_digits mem
                    (handle_sign_space mem (handle_whitespace mem p w))
                    d 0) \/
    z = - Z.of_nat (handle_digits mem
                     (handle_sign_space mem (handle_whitespace mem p w))
                     d 0).
Proof.
  intros mem p w d.
  unfold atoi.
  set (p_ws := handle_whitespace mem p w).
  set (p_start := handle_sign_space mem p_ws).
    destruct (handle_digits mem p_start d 0) as [| val].
      (* handle_digits = 0 *)
      left. reflexivity.
      (* handle_digits = S val *)
      right.
      set (z := handle_sign mem p_ws).
    destruct (Z.eq_dec z 1); try lia.
      right.
      assert (z = -1).
      { (* since z isnt 1, it must be -1 *)
        destruct (sign_value_correct mem p_ws).
          subst z. contradiction.
          subst z. assumption.
      }
      lia.
Qed.
