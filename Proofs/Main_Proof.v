(* Main atoi proof - ties together lifted source and all lemmas *)

Require Import Picinae_armv8_pcode.
Require Import Utf8.
Require Import NArith.
Require Import ZArith.
Require Import Lia.
(* Import the Lifted Source file *)
Require Import atoi_lo_atoi_armv8.
(* Import all lemmas *)
Require Import basic_properties.
Import ARM8Notations.

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
Definition atoi_exit (t:trace) : Prop :=
  match t with 
  | (Addr a,s)::_ => 
    match a with
    | 0x100070 => True
    | _ => False
    end 
  | _ => False 
  end.

Section Invariants.

  Variable mem : memory.
  Variable p : addr.

  (* ========== Helper Predicates ========== *)
  
  (* A byte is whitespace: 0x09-0x0d (tab through carriage return) or 0x20 (space) *)
  Definition is_whitespace (b : N) : Prop :=
    (0x09 <= b /\ b <= 0x0d) \/ b = 0x20.

  (* All bytes from index 0 to i-1 are whitespace *)
  Definition all_whitespace_until (i : N) : Prop :=
    ∀ j, j < i -> is_whitespace (mem Ⓑ[p+j]).

  (* A byte represents a decimal digit *)
  Definition is_digit (b : N) : Prop :=
    0x30 <= b /\ b <= 0x39.

  (* Convert ASCII digit to numeric value *)
  Definition digit_value (b : N) : N :=
    b - 0x30.

  (* All bytes from index j to j+k-1 are digits *)
  Definition all_digits (j k : N) : Prop :=
    ∀ i, i < k -> is_digit (mem Ⓑ[p+j+i]).

  (* The byte at position k is not a digit (terminator) *)
  Definition non_digit_terminator (j k : N) : Prop :=
    ¬(is_digit (mem Ⓑ[p+j+k])).

  (* ========== Specification Components ========== *)
  
  (* Index of first non-whitespace character *)
  Definition first_nonwhitespace (i : N) : Prop :=
    all_whitespace_until i /\ ¬(is_whitespace (mem Ⓑ[p+i])).

  (* w3 encodes the sign: 1 for negative, 0 for non-negative *)
  Definition sign_indicator (i : N) (w : N) : Prop :=
    (mem Ⓑ[p+i] = 0x2D /\ w = 1) \/  (* minus sign *)
    ((mem Ⓑ[p+i] = 0x2B \/ is_digit (mem Ⓑ[p+i])) /\ w = 0).  (* plus or digit *)

  (* Index where digits start (after optional sign) *)
  Definition digit_start (i : N) (j : N) : Prop :=
    (mem Ⓑ[p+i] = 0x2D \/ mem Ⓑ[p+i] = 0x2B) /\ j = i + 1 \/
    is_digit (mem Ⓑ[p+i]) /\ j = i.

  (* Number of digits following the sign *)
  Definition digit_count (j k : N) : Prop :=
    all_digits j k /\ non_digit_terminator j k.

  (* Convert a sequence of digits to an integer value
     Building from most significant to least significant *)
  Fixpoint digits_to_value_acc (j acc : N) (remaining : nat) : Z :=
    match remaining with
    | O => 0
    | S n' => 
      Z.of_N (digit_value (mem Ⓑ[p+j+acc])) + 
      10 * (digits_to_value_acc j (acc + 1) n')
    end.

  Definition digits_to_value (j k : N) : Z :=
    digits_to_value_acc j 0 (N.to_nat k).

  Definition bit_count_twos_complement (i : Z) : N :=
    match i with 
    | Z0 => 1
    | Z.pos n => N.succ (N.log2_up (N.succ (Npos n)))
    | Z.neg n => N.succ (N.log2_up (Npos n))
    (*| Z.pos n => N.log2_up (Npos (n + 1)) + 1
    | Z.neg n => N.log2_up (Npos n) + 1 *)
    end.
    
  Compute bit_count_twos_complement (2).
   
  
  Lemma pos_plus_succ: 
    forall (p : positive), Z.pos (Pos.succ p) = Z.pos (p + 1).
  Proof. 
    intros. induction p0.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.
  
  Lemma z_succ_of_n: 
    forall (n: N), Z.of_N (N.succ n) = Z.succ (Z.of_N n).
  Proof.
    destruct n.
    - reflexivity.
    - simpl. apply pos_plus_succ.
   Qed. 
   


  Lemma z_of_n_log2_up_comm: 
    forall (n: N), Z.of_N (N.log2_up n) = Z.log2_up (Z.of_N n).
  Proof.
    induction n.
    - reflexivity.
    - simpl. destruct (N.pos p0) eqn:Hp.
      + simpl. discriminate.
      + unfold N.log2_up, Z.log2_up. 
    admit.
  Admitted. (* Charles said to admit for the time being *)
    
  Lemma z_to_n_to_pos: 
    forall (p: positive), Z.of_N (N.pos p) = Z.pos(p).
  Proof.
    reflexivity.
  Qed.

    
  Lemma n_pos_succ_pos_comm: 
    forall (p : positive), N.pos (Pos.succ p) = N.succ (N.pos p).
  Proof.
    reflexivity.
  Qed.
  
  Print Z.log2_up_pow2.
  Lemma z_pow2_log2_up:
    forall (a: Z), (0 < a)%Z -> (2 ^ (Z.log2_up a))%Z = a.
  Proof.
    intros. induction a.
    - discriminate.
    - simpl. unfold Z.log2_up. simpl. admit.
    - simpl. discriminate.
  Admitted.
       
  (* forall signed integers z, bit_count will return an N s.t. -(2^N) <= z < 2^N *)
  Theorem bit_count_correctness: 
    forall (i : Z) (n : N), bit_count_twos_complement i = n -> (signed_range n i).
  Proof.
    induction i. 
    (* ZERO *)
    - simpl; unfold signed_range. lia.
    (* POSITIVE *)
    - simpl; unfold signed_range. intros.     
     rewrite <- H. rewrite z_succ_of_n. rewrite Z.pred_succ.
      rewrite N.pred_succ. simpl. split. (* rewrite z_of_n_log2_up_comm. simpl. split.*)
      + lia.
      + rewrite n_pos_succ_pos_comm. rewrite z_of_n_log2_up_comm. rewrite z_pow2_log2_up.
       -- lia.
       -- lia.
    (* NEGATIVE *)
    - simpl; unfold signed_range. intros. 
      rewrite <- H. rewrite z_succ_of_n. rewrite Z.pred_succ.
      rewrite N.pred_succ. simpl. split.
      + rewrite z_of_n_log2_up_comm. simpl. rewrite z_pow2_log2_up.
        -- lia.
        -- lia.
      + lia.
  Qed.

  (* ========== Post-condition ========== *)
  
  Definition postcondition (s : store) : Prop :=
    ∃ i w j k,
      first_nonwhitespace i /\
      sign_indicator i w /\
      digit_start i j /\
      digit_count j k /\
      let value := digits_to_value j k in
      let result : Z := if (w =? 1)%N then Z.opp value else value in
      ((Z.lt result (Z.of_N 2147483648) \/ Z.gt result (Z.of_N 2147483647)) \/  (* overflow case *)
      (Z.le 0 result /\ s R_X0 = Z.to_N result)).  (* normal case *)

  (* ========== Loop Invariants ========== *)

  (* Invariant at entry point (0x100000): Initialize *)
  Definition inv_entry (s : store) : Prop :=
    s R_X1 = p.  (* x1 points to input string *)

  (* Invariant at whitespace-skipping loop (0x100004): 
     We've skipped i characters, haven't found non-whitespace yet *)
  Definition inv_whitespace_loop (i : N) (s : store) : Prop :=
    all_whitespace_until i /\
    s R_X1 = p + i.

  (* Invariant at sign-check section (0x100018): 
     We've identified first non-whitespace, now checking for sign *)
  Definition inv_after_whitespace (i : N) (s : store) : Prop :=
    first_nonwhitespace i /\
    s R_X0 = mem Ⓑ[p+i] /\
    s R_X1 = p + i.

  (* Invariant at end (0x100070): Result finalized *)
  Definition inv_exit (i w j k : N) (s : store) : Prop :=
    first_nonwhitespace i /\
    sign_indicator i w /\
    digit_start i j /\
    digit_count j k /\
    let final_acc := digits_to_value j k in
    let result : Z := if (w =? 1)%N then Z.opp final_acc else final_acc in
    ((Z.lt result (Z.of_N 2147483648) \/ Z.gt result (Z.of_N 2147483647)) \/
    (Z.le 0 result /\ s R_X0 = Z.to_N result)).

  (* Invariant at digit-parsing loop (0x100058): 
     We're in the loop parsing digits. We know:
     - which characters are whitespace/sign/digits
     - how many digits we've processed so far (acc)
     - the current position and what we're examining
     - the sign indicator in X3
     X0 contains a partial result (exact formula depends on implementation details) *)
  Definition inv_digit_loop (i w j k acc : N) (s : store) : Prop :=
    first_nonwhitespace i /\
    sign_indicator i w /\
    digit_start i j /\
    all_digits j k /\  (* we've seen k valid digits so far *)
    acc <= k /\  (* acc is how many we've actually processed *)
    s R_X1 = p + j + acc /\
    s R_X3 = w /\  (* sign flag *)
    s R_X4 = 10.   (* multiplier *)

  (* Invariant at digit-computation phase (0x10004c):
     We've multiplied the accumulator by 10, now subtracting the digit value *)
  Definition inv_digit_multiply (i w j k acc : N) (s : store) : Prop :=
    first_nonwhitespace i /\
    sign_indicator i w /\
    digit_start i j /\
    all_digits j (acc + 1) /\  (* we know this digit is valid *)
    acc < k /\
    s R_X1 = p + j + acc /\
    s R_X2 = digit_value (mem Ⓑ[p+j+acc]) /\
    s R_X3 = w /\
    s R_X4 = 10.

  (* Unified invariant set at each checkpoint *)
  Definition atoi_invs (t : trace) : Prop :=
    match t with
    | (Addr a, s) :: _ => 
      match a with
      | 0x100000 => inv_entry s
      | 0x100004 => ∃ i, inv_whitespace_loop i s
      | 0x100018 => ∃ i, inv_after_whitespace i s
      | 0x100058 => ∃ i w j k acc, inv_digit_loop i w j k acc s
      | 0x10004c => ∃ i w j k acc, inv_digit_multiply i w j k acc s
      | 0x100070 => postcondition s
      | _ => True  (* other addresses are unconstrained *)
      end
    | _ => True
    end.

End Invariants.

(* ========== Correctness Theorems ========== *)

(* Main correctness theorem: 
   The lifted atoi program satisfies the specification at all trace endpoints *)
Theorem atoi_correctness :
  forall mem p,
    forall_traces_in atoi_lo_atoi_armv8 (fun t => atoi_exit t -> (atoi_invs mem p) t).
Proof.
  intros mem p.
  (* Unfold the definition of forall_traces_in *)
  unfold forall_traces_in.
  intros t XP.
  (* XP : exec_prog atoi_lo_atoi_armv8 t *)
  (* Goal: atoi_exit t -> atoi_invs mem p t *)
  intro EXIT.
  (* EXIT : atoi_exit t *)
  (* Goal: atoi_invs mem p t *)
  
  (* Unfold atoi_exit to understand what it means *)
  unfold atoi_exit in EXIT.
  (* At the exit point, we should be at address 0x100070 *)
  
  (* The strategy is to trace backwards through the execution,
     verifying that invariants are maintained at each checkpoint *)
  
  (* For now, we'll admit the main proof and focus on the structure *)
  admit.
Admitted.

(* Memory preservation: atoi does not corrupt memory *)
Theorem atoi_preserves_memory :
  forall_endstates atoi_lo_atoi_armv8 
    (fun _ s _ s' => s V_MEM64 = s' V_MEM64).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.

(* Call safety: atoi does not corrupt the return address register *)
Theorem atoi_preserves_lr :
  forall_endstates atoi_lo_atoi_armv8 
    (fun _ s _ s' => s R_X30 = s' R_X30).
Proof.
  apply noassign_prog_same.
  prove_noassign.
Qed.
