(* Main atoi correctness proof
   
   This file proves that the binary implementation atoi_lo_atoi_armv8
   satisfies the atoi specification defined in Specification.v
   
   The proof structure follows the conversation with Professor Hamlen:
   1. Define what a correct atoi implementation should do (via Gallina specification)
   2. Prove the binary implementation matches this specification
   3. Focus on partial correctness: IF atoi returns, THEN it returns the correct value
   4. Only prove correctness for valid inputs (caller's responsibility to provide valid input)
*)

(* Import standard libraries *)
Require Import Utf8.
Require Import NArith.
Require Import ZArith.
Require Import Lia.

(* Import the lifted binary *)
Require Import atoi_lo_atoi_armv8.

(* Import all helper modules *)
Require Import Whitespace.
Require Import Sign.
Require Import Digits.
Require Import BitWidth.
Require Import Specification.
Require Import Invariants.

(* Import Picinae notations/tactics *)
Require Import Picinae_armv8_pcode.
Import ARM8Notations.

Open Scope N.

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

(* ========== Correctness Theorems ========== *)

Ltac step := time arm8_step; try exact I.

(* A single byte will never have a value greater than 2^32. *)
Lemma mod_too_big_to_matter:
  forall p m, m Ⓑ[ p ] mod 2 ^ 32 = m Ⓑ[ p ].
Proof.
  intros. apply getmem_mod with (w:=64) (e:=LittleE) (n2:=4) (n1:=1) (m:=m) (a:=p).
Qed.

Lemma all_digits_pred:
  ∀ mem p j k, k > 0 -> all_digits mem p j k -> all_digits mem p j (k-1).
Proof.
Admitted.

Check is_digit.

Lemma all_digits_succ:
  ∀ mem p j k, all_digits mem p j (k+1) -> all_digits mem p j k /\ is_digit (mem Ⓑ[p ⊕ j ⊕ k]).
Proof.
  intros. split.
    apply all_digits_pred in H. psimpl in H. assumption.
    induction k.
      simpl. apply N.lt_gt with (n:=0) (m:=1). apply N.lt_0_1.

Theorem atoi_partial_correctness:
  forall s t s' x' mem p 
    (PRE: atoi_pre p s t x' s')
    (MEM: s V_MEM64 = mem),
  satisfies_all atoi_lo_atoi_armv8 (atoi_invs mem p) atoi_exit ((x',s')::t).
Proof.
  intros. destruct PRE as (ENTRY & MDL & RX1). unfold inv_entry in RX1. apply prove_invs.

  (* Base Case: Entry, 1048576 *)
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
    unfold inv_sign_exists. repeat split.
      (* Our knowledge of the whitespace is maintained. *)
      unfold all_whitespace_until; assumption. assumption.
      (* We just hit the sign indicator, so it exists (and is a plus sign). *)
      unfold sign_indicator_exists. right.
      apply Neqb_ok in BC. rewrite X0 in BC. rewrite mod_too_big_to_matter in BC. assumption.
      (* The contents of R_X1 are unchanged from the previous invariant. *)
      psimpl; assumption.
      (* R_X3 now contains either 0 or 1; in this case, 0 because it's a plus sign *)
      psimpl; left; reflexivity.
    (* BC: Character is NOT a plus sign *)
    step. step.
      (* BC0: Character is a minus sign *)
      step. intros. specialize PRE with (i:=i). 
      destruct PRE as (WS & REG); destruct WS as (NUMWS & NONWS); destruct REG as (X0 & X1).
      unfold inv_sign_exists. repeat split.
        (* Our knowledge of the whitespace is maintained. *)
        unfold all_whitespace_until; assumption. assumption.
        (* We just hit the sign indicator, so it exists (and is a minus sign). *)
        unfold sign_indicator_exists. left.
        apply Neqb_ok in BC0. rewrite X0 in BC0. rewrite mod_too_big_to_matter in BC0. assumption.
        (* The contents of R_X1 are unchanged from the previous invariant. *)
        psimpl; assumption.
        (* R_X3 now contains either 0 or 1; in this case, 1 because it's a minus sign *)
        psimpl; right; reflexivity.
      (* BC0: Character is NOT a minus sign (1048624) *)
      step. step. intros. specialize PRE with (i:=i). 
      destruct PRE as (WS & REG); destruct WS as (NUMWS & NONWS); destruct REG as (X0 & X1). 
      (* If we reach here, this is no sign indicator. The digits should start at the first non-whitespace index. *)
      exists i. unfold inv_post_sign. split.
        (* We know the index of digit start; it's where we are now ! *)
        unfold digit_start. split.
          (* Our knowledge of the whitespace is maintained. *)
          unfold first_nonwhitespace, all_whitespace_until. split; assumption.
          (* There is no sign indicator. *)
          right. unfold sign_indicator_exists. repeat split.
            (* The current character is neither a plus nor minus sign. *)
            apply N.eqb_neq in BC. rewrite X0 in BC. rewrite mod_too_big_to_matter in BC.
            apply N.eqb_neq in BC0. rewrite X0 in BC0. rewrite mod_too_big_to_matter in BC0.
            psimpl. psimpl in BC. psimpl in BC0. tauto. (* trust me bro *)
        (* We have seen 0 valid digits so far; base case for setting up the main loop *)
        split. unfold all_digits. intros. apply N.nlt_0_r in H. exfalso; assumption.
        (* R_X1 has not been incremented because there is no sign indicator, so it's already
           at the index at which digits should start. *)
        psimpl; assumption.

  (* 1048620 -> 1048624: There is a sign indicator. *)
  step. intros. specialize PRE with (i:=i). 
  destruct PRE as (WS & H); destruct H as (SIGN & H); destruct H as (X1 & X3).
  exists (i+1). unfold inv_post_sign. split.
    (* We know the index of digit start. 
       Since there is a sign indicator, it should be first nonwhitespace + 1. *)
    unfold digit_start. destruct WS as (WS & NONWS). repeat split.
      (* Our knowledge of the whitespace is maintained. *)
      assumption. assumption.
      (* We know a sign indicator exists. *)
      left. split.
        (* A valid sign indicator exists (it's a plus or minus sign). *)
        unfold sign_indicator_exists in *. assumption.
        (* Because a sign indicator exists, R_X3 is either 0 or 1, and the index of digit start is i+1. *)
        psimpl. split; try assumption; try reflexivity.
        (* We have seen 0 valid digits so far; base case for setting up the main loop *)
        split. unfold all_digits. intros. apply N.nlt_0_r in H. exfalso; assumption.
        (* Because a sign indicator exists, R_X1 is incremented at 1048620. *)
        psimpl. rewrite X1. psimpl; reflexivity.

  (* 1048624 -> 1048664: From the main loop setup (inv_post_sign) to inside the loop's conditional. *)
  step. step. step. intros.
  (* Precondition work *)
  specialize PRE with (i:=i); unfold inv_post_sign, inv_sign_exists, sign_indicator_exists in PRE.
  destruct PRE; destruct H as (DIGIT & X1); pose DIGIT as D2; destruct D2 as (WS & SIGN); 
  destruct WS as (WS & NONWS); rename x into j. destruct SIGN as [SIGN|SIGN].
    (* Sign indicator exists. *)
    destruct SIGN as (SIGN & X3); destruct X3 as (X3 & J). exists (i+1), 0. 
    unfold inv_digit_loop. split.
      (* We know the index of digit start, and that R_X1 contains the index of digit start. *)
      unfold inv_post_sign. split.
        (* We know the index of digit start. *)
        unfold digit_start. psimpl. repeat split.
          (* Our knowledge of the whitespace is maintained. *)
          assumption. assumption.
          (* Examine the case in which a sign indicator exists. *)
          left. split.
            (* A valid sign indicator exists. *)
            unfold sign_indicator_exists in *. assumption.
            (* R_X3 contains a 0 or a 1. *)
            psimpl; split; try assumption.
            (* The index of digit start is the first non-whitespace index + 1. *)
            reflexivity.
          (* We have seen 0 valid digits so far. *)
          split. subst. destruct X1; assumption.
          (* Because a sign indicator exists, j = i+1, and this is what R_X1 contains. *)
          subst. psimpl in X1; psimpl. destruct X1. split; try assumption; try reflexivity.
    (* Sign indicator does not exist. *)
    destruct SIGN as (SIGN & X3); destruct X3 as (X3 & J). exists i, 0.
    unfold inv_digit_loop. split.
      (* We know the index of digit start, and that R_X1 contains the index of digit start. *)
      unfold inv_post_sign. split.
        (* We know the index of digit start. *)
        unfold digit_start. psimpl. repeat split.
          (* Our knowledge of the whitespace is maintained. *)
          assumption. assumption.
          (* Examine the case in which no sign indicator exists. *)
          right. split.
            (* No sign indicator exists. *)
            unfold sign_indicator_exists in *. assumption.
            (* R_X3 contains a 0. *)
            split; try assumption.
            (* The index of digit start is the first non-whitespace index. *)
            reflexivity.
          (* We have seen 0 valid digits so far. *)
          split. subst. destruct X1; assumption.
          (* Because no sign indicator exists, j = i, and this is what R_X1 contains. *)
          subst. psimpl in X1; psimpl. destruct X1. split; try assumption; try reflexivity.

  (* 1048636 -> 1048580 - From inside whitespace loop back to the start of it*)
  step. step.
  specialize PRE with (i:=0). destruct PRE as (WSPRE & WS). destruct WS as (WS & X0 & X1).
  unfold inv_whitespace_loop, all_whitespace_until. exists 1. split.
    left. psimpl.
    psimpl. psimpl in WS. assumption.
    psimpl. rewrite X1. psimpl; reflexivity.

  (* 1048652 -> 1048664 *)
  admit.

  (* 1048664 -> 1048652 and 1048664 -> EXIT *)
  step. step. step. step.
    (* 1048664 -> EXIT *)
    admit. Print N.pos.
    (* 1048664 -> 1048652 *)
    (* Precondition unfolding *)
    intro i. specialize PRE with (i:=i). unfold inv_digit_loop, inv_post_sign in PRE.
    destruct PRE; rename x into j; destruct H; rename x into k;
    destruct H as (DSTART & H); destruct DSTART as (WS & SIGN); 
    destruct H as (ALLD & H); destruct H as (ACC & X4).
    rename p0 into x.
    (* Proof *)
    intros. unfold inv_digit_multiply; psimpl. exists j; exists k; exists k. split.
      (* digit_start i j s *)
      unfold digit_start in *. split.
        (* Whitespace knowledge is preserved *)
        assumption.
        destruct SIGN as [SIGN|SIGN].
          (* Case 1: Sign indicator exists. *)
          destruct SIGN as (SIGN & X3 & J). left; psimpl. unfold sign_indicator_exists in *.
          repeat split; try assumption. psimpl in J; assumption.
          (* Case 2: Sign indicator does not exist. *)
          destruct SIGN as (SIGN & X3 & J). right; psimpl. unfold sign_indicator_exists in *.
          repeat split; assumption.
      (* All bytes from j to j+1 are digits *)
      split. unfold all_digits.
      split. assumption.
      split. unfold digit_value. psimpl. 
      admit. admit.
Admitted.