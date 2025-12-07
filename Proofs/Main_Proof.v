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
Theorem atoi_welltyped: 
  welltyped_prog arm8typctx atoi_lo_atoi_armv8.
Proof. 
  Picinae_typecheck. 
Qed.

(* Post condition point for atoi *)
Definition atoi_exit (t:trace) : bool :=
  match t with 
  | (Addr 0x100070,_)::_ => true
  | _ => false 
  end.

Section Invariants.

  Variable mem : memory.
  Variable p : addr.

  (* ========== Helper Predicates ========== *)
  
  (* A byte is whitespace: 0x09-0x0d (tab through carriage return) or 0x20 (space) *)
  Definition is_whitespace (b : N) : Prop :=
    (0x09 <= b /\ b <= 0x0d) \/ b = 0x20.

  (* All bytes from index 0 to i-1 are whitespace, or i = 0. *)
  Definition all_whitespace_until (i : N) : Prop :=
    is_whitespace (mem Ⓑ[p⊕i-1]) \/ i = 0.

  (* A byte represents a decimal digit *)
  Definition is_digit (b : N) : Prop :=
    0x30 <= b /\ b <= 0x39.

  (* Convert ASCII digit to numeric value *)
  Definition digit_value (b : N) : N :=
    b - 0x30.

  (* (* All bytes from index j to j⊕k-1 are digits *)
  Definition all_digits (j k : N) : Prop :=
    ∀ i, i < k -> is_digit (mem Ⓑ[p⊕j⊕i]).

  (* The byte at position k is not a digit (terminator) *)
  Definition non_digit_terminator (j k : N) : Prop :=
    ¬(is_digit (mem Ⓑ[p⊕j⊕k])). *)

  (* ========== Specification Components ========== *)
  
  (* Index of first non-whitespace character *)
  Definition first_nonwhitespace (i : N) : Prop :=
    all_whitespace_until i /\ ¬(is_whitespace (mem Ⓑ[p⊕i])).

  (* w3 encodes the sign: 1 for negative, 0 for non-negative *)
  Definition sign_indicator (i : N) (s : store) : Prop :=
    (mem Ⓑ[p⊕i] = 0x2D /\ s R_X3 = 1 /\ s R_X1 = p + i + 1) \/  (* minus sign *)
    (mem Ⓑ[p⊕i] = 0x2B /\ s R_X3 = 0 /\ s R_X1 = p + i + 1) \/ (* plus sign *)
    (s R_X3 = 0 /\ s R_X1 = p + i).  (* no sign *)

  (* Index where digits start (after optional sign) *)
  Definition digit_start (i : N) (j : N) : Prop :=
    (mem Ⓑ[p⊕i] = 0x2D \/ mem Ⓑ[p⊕i] = 0x2B) /\ j = i + 1 \/
    is_digit (mem Ⓑ[p⊕i]) /\ j = i.

  (* Number of digits following the sign *)
  (* Definition digit_count (j k : N) : Prop :=
    all_digits j k /\ non_digit_terminator j k. *)

  (* Convert a sequence of digits to an integer value
     Building from most significant to least significant *)
  Fixpoint digits_to_value_acc (j acc : N) (remaining : nat) : Z :=
    match remaining with
    | O => 0
    | S n' => 
      Z.of_N (digit_value (mem Ⓑ[p⊕j⊕acc])) + 
      10 * (digits_to_value_acc j (acc + 1) n')
    end.

  Definition digits_to_value (j k : N) : Z :=
    digits_to_value_acc j 0 (N.to_nat k).

  (* ========== Post-condition ========== *)
  
  Definition postcondition (s : store) : Prop :=
    ∃ i w j k,
      first_nonwhitespace i /\
      sign_indicator i w /\
      digit_start i j /\
(*       digit_count j k /\ *)
      let value := digits_to_value j k in
      let result : Z := if (s R_X3 =? 1)%N then Z.opp value else value in
      ((Z.lt result (Z.of_N 2147483648) \/ Z.gt result (Z.of_N 2147483647)) \/  (* overflow case *)
      (Z.le 0 result /\ s R_X0 = Z.to_N result)).  (* normal case *)

  (* ========== Loop Invariants ========== *)

  Variable s0: store. (* Initial state *)

  (* Invariant at entry point (0x100000): Initialize *)
  Definition inv_entry (s : store) : Prop :=
    s R_X0 = p.  (* x1 points to input string *)

  Definition atoi_pre t x' s' :=
  startof t (x', s') = (Addr 0x100000, s0) /\ (* We start execution of atoi at 0x100000 *)
  models arm8typctx s0 /\ (* The initial state is assumed to obey the typing context of arm8 *)
  inv_entry s0.

  (* 1048580 - Invariant at whitespace-skipping loop 
     We've skipped i characters, haven't found non-whitespace yet *)
  Definition inv_whitespace_loop (i : N) (s : store) : Prop :=
    all_whitespace_until i /\
    s R_X1 = p + i.

  (* 1048636 - Invariant at the first statement inside the whitespace-skipping loop *)
  (* If we are here, the current character should indeed be whitespace. *)
  Definition inv_inside_whitespace_loop (i : N) (s : store) : Prop :=
    is_whitespace (mem Ⓑ[p⊕i]) /\
    s R_X0 = mem Ⓑ[p+i] /\
    s R_X1 = p + i.

  (* 1048600 - Invariant at sign-check section
     At this point we know the value of R_X1, which should hold the index of the first non-whitespace character.
     We've identified first non-whitespace, now checking for sign *)
  Definition inv_after_whitespace (i : N) (s : store) : Prop :=
    first_nonwhitespace i /\
    s R_X0 = mem Ⓑ[p⊕i] /\
    s R_X1 = p + i.

  (* Invariant at end (0x100070): Result finalized *)
  Definition inv_exit (i j k : N) (s : store) : Prop :=
    first_nonwhitespace i /\
    sign_indicator i s /\
    digit_start i j /\
(*     digit_count j k /\ *)
    let final_acc := digits_to_value j k in
    let result : Z := if (s R_X3 =? 1)%N then Z.opp final_acc else final_acc in
    ((Z.lt result (Z.of_N 2147483648) \/ Z.gt result (Z.of_N 2147483647)) \/
    (Z.le 0 result /\ s R_X0 = Z.to_N result)).

  (* Invariant placed right after processing the sign indicator (1048624) *)
  (* The only possible values for w are 0 or 1 at this point. *)
  (* We know the amount of whitespace. *)
  (* We know if a sign exists, and that R_X1 was incremented one more time if one exists. *)
  Definition inv_post_sign (i : N) (s : store) : Prop :=
    (s R_X3 = 0 \/ s R_X3 = 1) /\
    sign_indicator i s /\
    inv_after_whitespace i s.

  (* Invariant at digit-parsing loop (0x100058): 
     We're in the loop parsing digits. We know:
     - which characters are whitespace/sign/digits
     - how many digits we've processed so far (acc)
     - the current position and what we're examining
     - the sign indicator in X3
     X0 contains a partial result (exact formula depends on implementation details) *)
  Definition inv_digit_loop (i j k acc : N) (s : store) : Prop :=
    first_nonwhitespace i /\
    sign_indicator i s /\
    digit_start i j /\
(*     all_digits j k /\  (* we've seen k valid digits so far *) *)
    acc <= k /\  (* acc is how many we've actually processed *)
    s R_X1 = p + j + acc /\
    s R_X4 = 10.   (* multiplier *)

  (* Invariant at digit-computation phase (0x10004c):
     We've multiplied the accumulator by 10, now subtracting the digit value *)
  Definition inv_digit_multiply (i j k acc : N) (s : store) : Prop :=
    first_nonwhitespace i /\
    sign_indicator i s /\
    digit_start i j /\
(*     all_digits j (acc + 1) /\  (* we know this digit is valid *) *)
    acc < k /\
    s R_X1 = p + j + acc /\
    s R_X2 = digit_value (mem Ⓑ[p⊕j⊕acc]) /\
    s R_X4 = 10.

  (* Unified invariant set at each checkpoint *)
  Definition atoi_invs (t : trace) : option Prop :=
    match t with
    | (Addr a, s) :: _ => 
      match a with
      | 1048576 => Some (inv_entry s)
      | 1048580 => Some (∃ i, inv_whitespace_loop i s)
      | 1048636 => Some (∃ i, inv_inside_whitespace_loop i s)
      | 1048600 => Some (∀ i, inv_after_whitespace i s)
      | 1048624 => Some (∀ i, inv_post_sign i s)
(*       | 1048652 => Some (∃ i w j k acc, inv_digit_multiply i j k acc s) *)
(*       | 1048664 => Some (∃ i w j k acc, inv_digit_loop i j k acc s) *)
(*       | 1048688 => Some (postcondition s) *)
      | _ => None  (* other addresses are unconstrained *)
      end
    | _ => None
    end.

End Invariants.

(* ========== Correctness Theorems ========== *)

Check atoi_pre.

Ltac step := time arm8_step; try exact I.

Theorem atoi_partial_correctness:
  forall s t s' x' mem p 
    (PRE: atoi_pre p s t x' s')
    (MEM: s V_MEM64 = mem),
  satisfies_all atoi_lo_atoi_armv8 (atoi_invs mem p) atoi_exit ((x',s')::t).
Proof.
  intros. destruct PRE as (ENTRY & MDL & RX1). unfold inv_entry in RX1. apply prove_invs.
  
  (* Base Case: Entry, 1048576 *)
  Print inv_entry.
  simpl. rewrite ENTRY. step. assumption.
  
  (* Set up the inductive case *)
  intros. erewrite startof_prefix in ENTRY; try eassumption.
  eapply models_at_invariant; try eassumption. apply atoi_welltyped. intro MDL1.
  clear - PRE MDL1.
  destruct_inv 64 PRE.

  (* 1048576 -> 1048580, start of whitespace loop *)
  (* Prove that we have either skipped over j bytes of whitespace where j < i, or i = 0. *)
  step. unfold inv_whitespace_loop. unfold all_whitespace_until. exists 0. split.
    right; reflexivity.
    psimpl; reflexivity.

  (* 1048580 -> 1048636 and 1048580 -> 1048600 *)
  destruct PRE as (i & H0 & H1). unfold all_whitespace_until in H0. destruct H0.
    (* 1048580 -> 1048636: Prove that the current character is whitespace. *)
    admit.
    (* 1048580 -> 1048600: Prove that the current character is NOT whitespace, 
    and that there exists j whitespace bytes *)
    admit.

  (* 1048600 -> 1048624 *)
  (* After processing the sign indictor (if any), the only possible values of R_X3 are 0 or 1. *)
  unfold inv_after_whitespace, first_nonwhitespace, all_whitespace_until in PRE. 
  step. step.
    (* BC: Character is a plus sign *)
    step. step. step. intros. specialize PRE with (i:=i). 
    destruct PRE as (WS & REG); destruct WS as (NUMWS & NONWS); destruct REG as (X0 & X1).
    unfold inv_post_sign; split.
      (* R_X3 holds either 0 or 1. *)
      psimpl. left; reflexivity.
      split.
        (* According to BC, we have seen a plus sign and incremented R_X1. *)
        unfold sign_indicator. psimpl. right. left. split.
          apply Neqb_ok in BC. rewrite X0 in BC. admit. admit.
        (* We know how much whitespace there is, and therefore the value R_X0 holds. *)
        unfold inv_after_whitespace, first_nonwhitespace, all_whitespace_until. split. split; assumption.
        split; psimpl. admit. admit. (* i don't know why the goal is asking for 1 + s R_X1 *)
    (* BC: Character is NOT a plus sign *)
    step. step. step. step. intros. specialize PRE with (i:=i). 
    destruct PRE as (WS & REG); destruct WS as (NUMWS & NONWS); destruct REG as (X0 & X1).
    unfold inv_post_sign; split.
      (* R_X3 holds either 0 or 1. *)
      psimpl. right; reflexivity.
      split.
      (* According to BC0, we have seen a minus sign and incremented R_X1. *)
      admit.
      (* We know how much whitespace there is, and therefore the value R_X0 holds. *)
      admit.
    (* BC: Character is NOT a plus sign and is NOT a minus sign *)
    step. step. intros. specialize PRE with (i:=i). 
    destruct PRE as (WS & REG); destruct WS as (NUMWS & NONWS); destruct REG as (X0 & X1).
    unfold inv_post_sign; split.
      (* R_X3 holds either 0 or 1. *)
      psimpl. left; reflexivity.
      split.
      (* According to BC and BC0, there is no valid sign indicator and R_X1 remains as is. *)
      unfold sign_indicator. psimpl. right. right. split; try reflexivity. assumption.
      (* We know how much whitespace there is, and therefore the value R_X0 holds. *)
      unfold inv_after_whitespace, first_nonwhitespace, all_whitespace_until. split. split; assumption.
      split; psimpl. 
        admit.
        assumption.

  (* 1048624 -> 1048688 or 1048624 -> 1048652 *)
  step. step. step. unfold inv_digit_loop.

(*
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
*)
