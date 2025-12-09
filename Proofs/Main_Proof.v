(* Main atoi proof - ties together lifted source and all lemmas *)

Require Import Picinae_armv8_pcode.
Require Import Utf8.
Require Import NArith.
Require Import Lia.
(* Import the Lifted Source file *)
Require Import atoi_lo_atoi_armv8.
(* Import all lemmas *)
Require Import basic_properties.
Import ARM8Notations.
Open Scope N.


(* ARMv8 lifter creates non-writeable code *)
Theorem atoi_nwc:
  forall s1 s2, atoi_lo_atoi_armv8 s1 = atoi_lo_atoi_armv8 s2.
Proof.
  reflexivity.
Qed.

(* ARMv8 lifter produces well-typed IL *)
Theorem welltyped: 
  welltyped_prog arm8typctx atoi_lo_atoi_armv8.
Proof. 
  Picinae_typecheck. 
Qed.

(* Post condition point for atoi *)
Definition atoi_exit (t:trace) :=
  match t with 
  | (Addr a,s)::_ => 
    match a with
    | 0x100070 => true
    | _ => false
    end 
  | _ => false 
  end.

Section Invariants.

  Variable mem : memory.
  Variable p : addr.

  (* atoi returns a number n such that:
     - s[i] is the first place where we do not have whitespace
     - n is negative if s[i] == -
     - n is positive otherwise (s[i] == + or is just a digit)
     - if s[i] is + or -, then j = i + 1, else j = i
     - n consists of k digits from s[j] to s[j+k], where s[j+k+1] is a non-digit
  *)
  
  (* First i bytes are whitespace *)
  Definition whitespace (i:N) :=
    ∀ j, j < i -> mem Ⓑ[p+j] = 0x20 \/ mem Ⓑ[p+j] = 0xd.
    
  Definition isDigit (x : N) : Prop :=
    (x >= 0x30 /\ x <= 0x39) -> True.
    
  (* if s[i] is -, then w=1, else if s[i] is + or a digit then w=0 *)
  Definition w3_sign_value (w:N) := (* maybe we change this name probably perhaps *)
    ∃ i, (mem Ⓑ[p+i]=0x2D /\ whitespace i -> w=1) \/ 
         (whitespace i /\ 
            (mem Ⓑ[p+i]=0x2B \/ isDigit(mem Ⓑ[p+i])) -> w=0).
  
  (* if s[i] is + or -, then j = i + 1, else j = i *)
  Definition sign_exists (j:N) :=
    ∃ i, (whitespace i /\ (mem Ⓑ[p+i]=0x2D \/ mem Ⓑ[p+i]=0x2B) -> j=i+1)
         \/ whitespace i -> j=i.

  (* n consists of k digits from s[j] to s[j+k], where s[j+k+1] is a non-digit *)
  Definition k_digits (k:N) :=
    ∃ i j, i < k /\ sign_exists j -> isDigit(mem Ⓑ[p+j+i]).


  (* n is the number stored at s[j] to s[j+k] *)
  Definition postcondition (s:store) :=
    ∃ i w j k n, 
      whitespace i /\
      w3_sign_value w /\
      sign_exists j /\
      k_digits k /\
      (* n = mem Ⓑ[p+i] to mem Ⓑ[p+k] /\  (* not sure how to define this *) *)
      s R_X0 = n.


(* invariant definitions here *)


End Invariants.



(* Test that lifted source import is working *)
Lemma test_lifted_import : atoi_lo_atoi_armv8 = atoi_lo_atoi_armv8.
Proof.
  destruct (atoi_lo_atoi_armv8).
  - admit.
  - admit.
  - reflexivity.
  - reflexivity.
Admitted.

(* Test that lemmas import is working *)
Lemma test_lemmas_import : forall (x : N), x = x.
Proof.
  exact test_import.
Qed.

(* Main theorem will go here *)
(* Theorem atoi_correctness : ... *)
