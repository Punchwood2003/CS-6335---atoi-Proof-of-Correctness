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