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
    is_whitespace (mem Ⓑ[p ⊕ i ⊖ 1]) \/ i = 0.

  (* A byte represents a decimal digit *)
  Definition is_digit (b : N) : Prop :=
    0x30 <= b /\ b <= 0x39.

  (* Convert ASCII digit to numeric value *)
  Definition digit_value (b : N) : N :=
    b - 0x30.

  (* All bytes from index j to j⊕k-1 are digits *)
  Definition all_digits (j k : N) : Prop :=
    ∀ i, i < k -> is_digit (mem Ⓑ[p ⊕ j ⊕ i]).

  (* The byte at position k is not a digit (terminator) *)
  Definition non_digit_terminator (j k : N) : Prop :=
    ¬(is_digit (mem Ⓑ[p ⊕ j ⊕ k])).

  (* ========== Specification Components ========== *)
  
  (* Index of first non-whitespace character *)
  Definition first_nonwhitespace (i : N) : Prop :=
    all_whitespace_until i /\ ¬(is_whitespace (mem Ⓑ[p ⊕ i])).

  (* w3 encodes the sign: 1 for negative, 0 for non-negative *)
  Definition sign_indicator_exists (i : N) (s : store) : Prop :=
    (mem Ⓑ[p ⊕ i] = 0x2D /\ s R_X3 = 1) \/  (* minus sign *)
    (mem Ⓑ[p ⊕ i] = 0x2B /\ s R_X3 = 0).    (* plus sign *)

  (* Index where digits should start (after optional sign) *)
  Definition digit_start (i : N) (j : N) (s : store) : Prop :=
    (sign_indicator_exists i s /\ j = i + 1) \/
    (¬sign_indicator_exists i s /\ j = i).

  (* Number of digits following the sign *)
  (* Definition digit_count (j k : N) : Prop :=
    all_digits j k /\ non_digit_terminator j k. *)

  (* Convert a sequence of digits to an integer value
     Building from most significant to least significant *)
  Fixpoint digits_to_value_acc (j acc : N) (remaining : nat) : Z :=
    match remaining with
    | O => 0
    | S n' => 
      Z.of_N (digit_value (mem Ⓑ[p ⊕ j ⊕ acc])) + 
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
      sign_indicator_exists i w /\
      digit_start i j s /\
(*       digit_count j k /\ *)
      let value := digits_to_value j k in
      let result : Z := if (s R_X3 =? 1)%N then Z.opp value else value in
      ((Z.lt result (Z.of_N 2147483648) \/ Z.gt result (Z.of_N 2147483647)) \/  (* overflow case *)
      (Z.le 0 result /\ s R_X0 = Z.to_N result)).  (* normal case *)

  (* ========== Loop Invariants ========== *)

  Variable s0: store. (* Initial state *)

  (* 1048576 - Invariant at entry point
     The only thing we know at the entry point is that x0 points to input string.
     After the first instruction is executed, x1 will also point to the input string. *)
  Definition inv_entry (s : store) : Prop :=
    s R_X0 = p.

  Definition atoi_pre t x' s' :=
    startof t (x', s') = (Addr 0x100000, s0) /\ (* We start execution of atoi at 0x100000 *)
    models arm8typctx s0 /\ (* The initial state is assumed to obey the typing context of arm8 *)
    inv_entry s0.

  (* 1048580 - Invariant at whitespace-skipping loop 
     We've skipped i characters, haven't found non-whitespace yet *)
  Definition inv_whitespace_loop (i : N) (s : store) : Prop :=
    all_whitespace_until i /\
    s R_X1 = p ⊕ i.

  (* 1048636 - Invariant at the first statement inside the whitespace-skipping loop *)
  (* If we are here, the current character should indeed be whitespace. *)
  Definition inv_inside_whitespace_loop (i : N) (s : store) : Prop :=
    is_whitespace (mem Ⓑ[p ⊕ i]) /\
    s R_X0 = mem Ⓑ[p ⊕ i] /\
    s R_X1 = p ⊕ i.

  (* 1048600 - Invariant at sign-check section
     At this point we know how much whitespace there is.
     R_X0 should hold the first non-whitespace character, and
     R_X1 should hold the index of the first non-whitespace character. *)
  Definition inv_after_whitespace (i : N) (s : store) : Prop :=
    first_nonwhitespace i /\
    s R_X0 = mem Ⓑ[p ⊕ i] /\
    s R_X1 = p ⊕ i.

  (* 1048620 - Invariant after parsing an existing sign character.
     If we are here, there for sure is a sign indicator.\
     Therefore, we know the index at which digits should start appearing. *)
  Definition inv_sign_exists (i j : N) (s : store) : Prop :=
    sign_indicator_exists i s /\
    digit_start i j s /\
    s R_X1 = p ⊕ i.

  (* 1048624 - Invariant placed right after processing the sign indicator (1048624). We know that EITHER:
     1. A sign exists and R_X3 is either 0 or 1, or
     2. A sign does not exist and R_X3 is 0. 
     We also know where the digits should start based on the whitespace and sign existence. *)
  Definition inv_post_sign (i j : N) (s : store) : Prop :=
    ((sign_indicator_exists i s /\ (s R_X3 = 0 \/ s R_X3 = 1)) \/ 
    (¬(sign_indicator_exists i s) /\ s R_X3 = 0)) /\
    digit_start i j s /\
    s R_X1 = p ⊕ j.

  (* 1048664 - Invariant at digit-parsing loop: 
     We're in the loop parsing digits. We know:
     - which characters are whitespace/sign/digits
     - how many digits we've processed so far (acc)
     - the current position and what we're examining
     - the sign indicator in X3
     X0 contains a partial result (exact formula depends on implementation details) *)
  Definition inv_digit_loop (i j k acc : N) (s : store) : Prop :=
    inv_post_sign i j s /\
    all_digits j k /\  (* we've seen k valid digits so far *)
    acc <= k /\  (* acc is how many we've actually processed *)
    s R_X1 = p ⊕ j ⊕ acc /\
    s R_X4 = 10.   (* multiplier *)

  (* 1048652 - Invariant at digit-computation phase
     We've multiplied the accumulator by 10, now subtracting the digit value *)
  Definition inv_digit_multiply (i j k acc : N) (s : store) : Prop :=
    first_nonwhitespace i /\
    sign_indicator_exists i s /\
    digit_start i j s /\
    all_digits j (acc + 1) /\  (* we know this digit is valid *)
    acc < k /\
    s R_X1 = p ⊕ j ⊕ acc /\
    s R_X2 = digit_value (mem Ⓑ[s R_X1]) /\
    s R_X4 = 10.

  (* 1048688 - Invariant at return *)
  Definition inv_exit (i j k : N) (s : store) : Prop :=
    first_nonwhitespace i /\
    sign_indicator_exists i s /\
    digit_start i j s /\
(*     digit_count j k /\ *)
    let final_acc := digits_to_value j k in
    let result : Z := if (s R_X3 =? 1)%N then Z.opp final_acc else final_acc in
    ((Z.lt result (Z.of_N 2147483648) \/ Z.gt result (Z.of_N 2147483647)) \/
    (Z.le 0 result /\ s R_X0 = Z.to_N result)).

  (* Unified invariant set at each checkpoint *)
  Definition atoi_invs (t : trace) : option Prop :=
    match t with
    | (Addr a, s) :: _ => 
      match a with
      | 1048576 => Some (inv_entry s)
      | 1048580 => Some (∃ i, inv_whitespace_loop i s)
      | 1048636 => Some (∀ i, inv_inside_whitespace_loop i s)
      | 1048600 => Some (∀ i, inv_after_whitespace i s)
      | 1048620 => Some (∀ i, ∃ j, inv_sign_exists i j s)
      | 1048624 => Some (∀ i, ∃ j, inv_post_sign i j s)
      | 1048652 => Some (∀ i k acc, ∃ j, inv_digit_multiply i j k acc s)
      | 1048664 => Some (∀ i, ∃ j k acc, inv_digit_loop i j k acc s)
(*       | 1048688 => Some (postcondition s) *)
      | _ => None  (* other addresses are unconstrained *)
      end
    | _ => None
    end.

End Invariants.

(* ========== Correctness Theorems ========== *)

Ltac step := time arm8_step; try exact I.

(* A single byte will never have a value greater than 2^32. *)
Lemma mod_too_big_to_matter:
  forall p m, m Ⓑ[ p ] mod 2 ^ 32 = m Ⓑ[ p ].
Proof.
  intros. apply getmem_mod with (w:=64) (e:=LittleE) (n2:=4) (n1:=1) (m:=m) (a:=p).
Qed.

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

  (* 1048600 -> 1048620 and 1048600 -> 1048624 *)
  unfold inv_after_whitespace, first_nonwhitespace, all_whitespace_until in PRE.
  step. step.
    (* BC: Character is a plus sign, so we know a sign exists. *)
    step. step. intros. specialize PRE with (i:=i). 
    destruct PRE as (WS & REG); destruct WS as (NUMWS & NONWS); destruct REG as (X0 & X1).
    unfold inv_sign_exists. exists (i+1). split. right. split.
      (* The current character is in fact a plus sign *)
      apply Neqb_ok in BC. rewrite X0 in BC. rewrite mod_too_big_to_matter in BC. assumption.
      (* R_X3 is equal to 0 because this is a plus sign (positive number). *)
      psimpl; reflexivity.
      (* We know at what index the digits should start. *)
      unfold digit_start, first_nonwhitespace, all_whitespace_until. repeat split; try assumption.
      left. split.
        unfold sign_indicator_exists. right. split.
          apply Neqb_ok in BC. rewrite X0 in BC. rewrite mod_too_big_to_matter in BC. assumption.
          psimpl. reflexivity.
        reflexivity.
    (* BC: Character is NOT a plus sign *)
    step. step.
      (* BC0: Character is a minus sign *)
      step. intros. specialize PRE with (i:=i). 
      destruct PRE as (WS & REG); destruct WS as (NUMWS & NONWS); destruct REG as (X0 & X1).
      unfold inv_sign_exists. unfold sign_indicator_exists. exists (i+1). split. left. split.
        (* The current character is in fact a minus sign *)
        apply Neqb_ok in BC0. rewrite X0 in BC0. rewrite mod_too_big_to_matter in BC0. assumption.
        (* The current character is in fact a minus sign *)
        psimpl; reflexivity.
        (* We know at what index the digits should start. *)
        unfold digit_start. split. unfold first_nonwhitespace, all_whitespace_until. left. split.
          unfold sign_indicator_exists. left. split.
            apply Neqb_ok in BC0. rewrite X0 in BC0. rewrite mod_too_big_to_matter in BC0. assumption.
            psimpl; reflexivity.
          reflexivity.
        psimpl; assumption.
      (* BC0: Character is NOT a minus sign *)
      step. step. intros. specialize PRE with (i:=i). 
      destruct PRE as (WS & REG); destruct WS as (NUMWS & NONWS); destruct REG as (X0 & X1). exists i.
      unfold inv_post_sign. (* At this point, there is no sign indicator. *) split. right. split.
        (* There is no sign indicator. *)
        unfold sign_indicator_exists.
        apply N.eqb_neq in BC. rewrite X0 in BC. rewrite mod_too_big_to_matter in BC.
        apply N.eqb_neq in BC0. rewrite X0 in BC0. rewrite mod_too_big_to_matter in BC0.
        psimpl. psimpl in BC. psimpl in BC0. tauto. (* trust me bro *)
        (* R_X3 = 0 because there is no sign indicator. *)
        psimpl; reflexivity.
        (* We know at what index the digits should start. *)
        unfold digit_start. split.
          unfold sign_indicator_exists. right. split.
            apply N.eqb_neq in BC. rewrite X0 in BC. rewrite mod_too_big_to_matter in BC.
            apply N.eqb_neq in BC0. rewrite X0 in BC0. rewrite mod_too_big_to_matter in BC0.
            psimpl. psimpl in BC. psimpl in BC0. tauto.
          reflexivity.
        psimpl; assumption.

  (* 1048620 -> 1048624: There is a sign indicator. *)
  step. intros. 
  (* Precondition unfolding *)
  specialize PRE with (i:=i). destruct PRE. rename x into j; exists j. 
  unfold inv_sign_exists in H. destruct H as (SIGN & DIGIT). destruct DIGIT as (DIGIT & X1).
  (* Goal unfolding *)
  unfold inv_post_sign, inv_sign_exists.
  (* The Proof *)
  split. 
    (* There is a sign indicator and we know R_X3 is 0 or 1. *)
    left. split.
      (* There is a sign indicator. *)
      unfold sign_indicator_exists in *. destruct SIGN as [SIGN|].
        (* The sign was a minus sign. *)
        destruct SIGN as (SIGN & X3). left; split; assumption.
        (* The sign was a plus sign. *)
        destruct H as (SIGN & X3). right; split; assumption.
      (* R_X3 is either 0 or 1. *)
      psimpl. destruct SIGN. 
        destruct H. right; assumption.
        destruct H. left; assumption.
    (* We know the index of digit start. *)
    destruct DIGIT.
      (* A sign indicator exists; the index of digit start is just after this sign indicator. *)
      split.
        unfold digit_start. left. split.
          unfold sign_indicator_exists in *. psimpl. psimpl in SIGN. assumption.
          destruct H. assumption.
        psimpl. destruct H. subst. rewrite X1. psimpl; reflexivity.
      (* A sign indicator does NOT exist. *)
      destruct H. contradiction.

  (* 1048624 -> 1048664 *)
  step. step. step. intros. 
  specialize PRE with (i:=i); unfold inv_post_sign, inv_sign_exists, sign_indicator_exists in PRE.
  psimpl in PRE. destruct PRE; destruct H as (PRE & DSTART). rename x into j. destruct DSTART as (DSTART & X1).
  destruct PRE.
  (* Sign indicator exists. *)
  exists j, 0, 0. unfold inv_digit_loop. split.
    (* We know inv_post_sign still holds despite R_X0 and R_X4 being changed. *)
    unfold inv_post_sign. split. 
      unfold sign_indicator_exists. psimpl. left. assumption.
      split; assumption.
    (* We have seen k=0 valid digits so far. *)
    split.
      unfold all_digits. intros. apply N.nlt_0_r in H0. exfalso; assumption.
    split.
      apply N.le_refl.
      psimpl. split.
        assumption.
        reflexivity.
  (* Sign indicator does not exist. *)
  exists j, 0, 0. unfold inv_digit_loop. split.
    (* We know inv_post_sign still holds despite R_X0 and R_X4 being changed. *)
    unfold inv_post_sign. split. 
      unfold inv_sign_exists, sign_indicator_exists. psimpl. right. assumption. 
      split; assumption.
    (* We have seen k=0 valid digits so far. *)
    split.
      unfold all_digits. intros. apply N.nlt_0_r in H0. exfalso; assumption.
    split.
      apply N.le_refl.
      psimpl. split.
        assumption. 
        reflexivity.

  (* 1048636 -> 1048580 - From inside whitespace loop back to the start of it*)
  step. step. 
  specialize PRE with (i:=0). destruct PRE; psimpl in H. destruct H0.
  unfold inv_whitespace_loop, all_whitespace_until. exists 1. split.
    left. psimpl; assumption.
    psimpl. rewrite H1. psimpl; reflexivity.

  (* 1048652 -> 1048664 *)
  step. step. step. admit.

  (* 1048664 -> 1048652 and 1048664 -> EXIT *)
  admit.
Admitted.
