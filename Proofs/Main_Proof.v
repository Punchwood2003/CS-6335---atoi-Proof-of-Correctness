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

Lemma zero_lor_zero:
  forall n m, n .| m = 0 -> n = 0 /\ m = 0.
Proof.
  intros. split.
    apply N.lor_eq_0_l with (b:=m); assumption.
    rewrite N.lor_comm in H. apply N.lor_eq_0_l with (b:=n); assumption.
Qed.

Lemma trivial_if:
  forall (n m : N) (b : bool), (n ≠ m) -> (if b then n else m) = n -> b = true.
Proof.
  intros.
  destruct b.
    reflexivity.
    symmetry in H0; contradiction.
Qed.

Lemma trivial_if_false:
  forall (b : bool), (if b then 1 else 0) = 0 -> b = false.
Proof.
  intros.
  destruct b.
    discriminate.
    reflexivity.
Qed.

Lemma lor_0_or_1:
  forall (b1 b2 : bool) (n : N), 
    (if b1 then 0 else 1) .| (if b2 then 1 else 0) = n -> n = 0 \/ n = 1.
Proof.
  intros. destruct b1.
    destruct b2.
      right; simpl in H; symmetry; assumption.
      left; simpl in H; symmetry; assumption.
    destruct b2.
      right; simpl in H; symmetry; assumption.
      right; simpl in H; symmetry; assumption.
Qed.

Lemma lor_1_three_cases:
  forall (b1 b2 : bool), 
    (if b1 then 0 else 1) .| (if b2 then 1 else 0) = 1 -> (b1 = true /\ b2 = true) \/ (b1 = false /\ b2 = true) \/ (b1 = false /\ b2 = false).
Proof.
  intros. destruct b1 eqn:B1.
    destruct b2 eqn:B2.
      left. split; reflexivity.
      simpl in H. discriminate.
    destruct b2 eqn:B2.
      right. left. split; reflexivity.
      right. right. split; reflexivity.
Qed.

Lemma get_rid_of_pos:
  forall (b : bool) (n m x : N),
    (if b then n else m) = x -> x = n \/ x = m.
Proof.
  intros.
  destruct b.
    left; symmetry; assumption.
    right; symmetry; assumption.
Qed.

Lemma msub_lt_9:
  forall n, msub 32 n 48 < 9 -> 48 <= n < 57.
Admitted.

Lemma msub_mod_irrelevant:
  forall n, 48 <= n < 57 -> msub 32 n 48 = n - 48.
Admitted.

Ltac digit_start_persists DSTART := 
  unfold digit_start in *; destruct DSTART as (WS & SIGN); split;
    try assumption;
    destruct SIGN as [SIGN|NOSIGN];
      destruct SIGN as (SIGN & X3 & J); left; split;
        unfold sign_indicator_exists in *; try assumption;
        split; psimpl;
          try assumption;
          psimpl in J; assumption;
      destruct NOSIGN as (NOSIGN & X3 & J); right; split;
        unfold sign_indicator_exists in *; try assumption;
        split; psimpl;
          try assumption;
          psimpl in J; try assumption.

Check atoi_pre.

Theorem atoi_partial_correctness:
  forall s t s' x' mem p 
    (PRE: atoi_pre mem p s t x' s')
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
  step. destruct PRE as (X0 & MEM). unfold inv_whitespace_loop. unfold all_whitespace_until. exists 0. split.
    right; reflexivity.
    split.
      psimpl; assumption.
      psimpl; assumption.

  (* 1048580 -> 1048636 and 1048580 -> 1048600 *)
  destruct PRE as (i & H0 & H1 & MEM).
    (* 1048580 -> 1048636: Prove that the current character is whitespace. *)
    step. step. step. step. step. exists i. unfold inv_inside_whitespace_loop.
    (* Case 1: The current character is a space (32). *)
      (* We have seen i whitespace bytes so far *)
      split. assumption.
      (* The current character is whitespace. *)
      split. unfold is_whitespace. right; psimpl. apply Neqb_ok in BC; assumption.
      (* The contents of R_X0 are unchanged. *)
      repeat split; psimpl. reflexivity.
    (* Case 2: The current character is NOT a space (32), and is instead 0x9 <= x <= 0xd. *)
      step. apply zero_lor_zero in BC0. destruct BC0 as (GE9 & LE13).
        apply trivial_if in GE9; apply trivial_if_false in LE13.
        2: unfold "~"; intros; discriminate.
      intros. unfold inv_after_whitespace.
      (* first_nonwhitespace *)
      split. unfold first_nonwhitespace.
    (* 1048580 -> 1048600: Prove that the current character is NOT whitespace, 
    and that there exists j whitespace bytes *)
    admit. admit. admit.

  (* 1048600 -> 1048620 and 1048600 -> 1048624 *)
  unfold inv_after_whitespace, first_nonwhitespace, all_whitespace_until in PRE.
  step. step.
    (* BC: Character is a plus sign, so we know a sign exists. *)
    step. step. intros. specialize PRE with (i:=i). 
    destruct PRE as (WS & X0 & X1 & MEM); destruct WS as (WS & NONWS).
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
      (* MEM *)
      psimpl; assumption.
    (* BC: Character is NOT a plus sign *)
    step. step.
      (* BC0: Character is a minus sign *)
      step. intros. specialize PRE with (i:=i). 
      destruct PRE as (WS & X0 & X1 & MEM); destruct WS as (WS & NONWS).
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
        (* MEM *)
        psimpl; assumption.
      (* BC0: Character is NOT a minus sign (1048624) *)
      step. step. intros. specialize PRE with (i:=i). 
      destruct PRE as (WS & X0 & X1 & MEM); destruct WS as (WS & NONWS).
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
        split. psimpl; assumption.
        (* MEM *)
        psimpl; assumption.

  (* 1048620 -> 1048624: There is a sign indicator. *)
  step. intros. specialize PRE with (i:=i).
  destruct PRE as (WS & SIGN & X1 & X3 & MEM).
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
        psimpl. rewrite X1. split. psimpl; reflexivity.
        (* MEM *)
        psimpl; assumption.

  (* 1048624 -> 1048664: From the main loop setup (inv_post_sign) to inside the loop's conditional. *)
  step. step. step. intros.
  (* Precondition work *)
  specialize PRE with (i:=i).
  destruct PRE; rename x into j. destruct H as (DSTART & ALLD & X1 & MEM); destruct DSTART as (WS & SIGN). 
  destruct SIGN as [SIGN|SIGN].
    (* Sign indicator exists. *)
    destruct SIGN as (SIGN & X3); destruct X3 as (X3 & J). exists (i+1), 0. 
    unfold inv_digit_loop. split.
      (* We know the index of digit start, and that R_X1 contains the index of digit start. *)
      unfold inv_post_sign. split.
        (* We know the index of digit start. *)
        unfold digit_start. psimpl.
          (* Our knowledge of the whitespace is maintained. *)
          assumption.
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
          subst. psimpl in X1; psimpl. repeat split; try assumption.
    (* Sign indicator does not exist. *)
    destruct SIGN as (SIGN & X3); destruct X3 as (X3 & J). exists i, 0.
    unfold inv_digit_loop. split.
      (* We know the index of digit start, and that R_X1 contains the index of digit start. *)
      unfold inv_post_sign. split.
        (* We know the index of digit start. *)
        unfold digit_start. psimpl.
          (* Our knowledge of the whitespace is maintained. *)
          assumption.
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
          subst. psimpl in X1; psimpl. repeat split; try assumption.

  (* 1048636 -> 1048580 - From inside whitespace loop back to the start of it *)
  admit.

  (* 1048652 -> 1048664 *)
  (* Setup *)
  step. step. step. intros. specialize PRE with (i:=i). destruct PRE; destruct H; destruct H.
  rename x into j; rename x0 into k; rename x1 into acc. exists j, (k+1).
  unfold inv_digit_multiply in H. destruct H as (DSTART & ALLD & ISDIGIT & X1 & X2 & X4 & MEM).
  (* Proof *)
  unfold inv_digit_loop. split.
    (* The digit start index remains the same. *)
    digit_start_persists DSTART.
    (* all_digits *)
    split. apply inductive_all_digits; assumption.
    (* X1 *)
    split. psimpl. rewrite X1. psimpl; reflexivity.
    (* X4 *)
    split. psimpl; assumption.
    (* MEM *)
    psimpl; assumption.

  (* 1048664 -> 1048652 and 1048664 -> 1048680 *)
  step. step. step. step.
    (* ixb, look here *)
    (* 1048664 -> 1048680 - We do NOT take the b.ls branch *)
    intro i. specialize PRE with (i:=i). destruct PRE; destruct H. rename x into j; rename x0 into k.
    apply zero_lor_zero in BC. destruct BC as (BC1 & BC2). 
    apply trivial_if in BC1. apply trivial_if_false in BC2.
    unfold inv_digit_loop in H. destruct H as (DSTART & ALLD & X1 & X4 & MEM).
    exists j, k. unfold inv_post_digit_loop. split.
      (* The digit start index remains the same. *)
      digit_start_persists DSTART.
      (* We know there are k-j valid digits. *)
      split; try assumption.
      (* The current character is not a digit, and that's why we have terminated the loop. *)
      split. unfold is_digit. rewrite <- X1. rewrite MEM in *. apply N.eqb_neq in BC2.
      unfold "~". intros. apply N.leb_le in BC1. destruct H as (GE48 & LE57).
      apply digits_msub with (n := mem Ⓑ[ s1 R_X1 ]) in BC1; assumption.
      (* MEM *)
      psimpl; assumption.
      (* Cleaup from using trivial_if *)
      unfold "~"; intros; discriminate.
    (* 1048664 -> 1048652 - We take the b.ls branch *)
    (* Precondition unfolding *)
    intro i. specialize PRE with (i:=i). unfold inv_digit_loop, inv_post_sign in PRE.
    destruct PRE; rename x into j; destruct H; rename x into k;
    destruct H as (DSTART & H); 
    destruct H as (ALLD & H); destruct H as (ACC & X4 & MEM).
    rename p0 into x.
    (* Working with the branch condition *)
    pose BC as X. apply lor_0_or_1 in X. destruct X as [X|X].
      rewrite X in BC. apply zero_lor_zero in BC. destruct BC as (BC1 & BC2). rewrite MEM in *.
      apply trivial_if in BC1. apply trivial_if_false in BC2. rewrite BC1. rewrite BC2.
        2: unfold "~"; intros; discriminate.
      (* This case is already handled above in the proof for 1048664 -> 1048680.
         It's impossible for this case to arise and for the code to also branch. 
         After the above simplification, CF = 1 and ZF = 0. b.ls branches if CF = 0 OR ZF = 1,
         meaning it's impossible for this branch to have occurred.

         However, I don't know how to prove that and will just admit this case.
         *)
      admit.
      (* Complete the other 3 possible cases *) 
      rewrite X in BC. clear X. apply lor_1_three_cases in BC. destruct BC as [BC|[BC|BC]]. 
        destruct BC as (BC1 & BC2); apply N.eqb_eq in BC2. exists j, k, j. unfold inv_digit_multiply. split.
          (* digit_start *)
          digit_start_persists DSTART.
          (* all_digits *)
          split. assumption.
          (* Prove the current digit is in fact a digit, because we're in the loop. *)
          split. rewrite MEM in *. unfold is_digit; split; rewrite <- ACC; rewrite BC2.
            apply N.le_sub_l with (n:=57) (m:=9).
            reflexivity.
          (* X1 holds the index of the current char. *)
          split. psimpl; psimpl in ACC. assumption.
          (* X2 holds the digit value of the current char. *)
          split. psimpl. rewrite BC2. unfold digit_value. psimpl. rewrite MEM in *. rewrite BC2.
          reflexivity.
          (* X4 is 10 (the multiplier). *)
          split. psimpl; assumption.
          (* MEM *)
          psimpl; assumption.
        destruct BC as (BC1 & BC2); apply N.eqb_eq in BC2. exists j, k, j. unfold inv_digit_multiply.
          (* digit_start *)
          split. digit_start_persists DSTART.
          (* all_digits *)
          split. assumption.
          (* Prove the current digit is in fact a digit, because we're in the loop. *)
          split. rewrite MEM in *. apply N.leb_gt in BC1. rewrite BC2 in BC1. 
          assert (msub 32 57 48 = 9). reflexivity. rewrite H in BC1. apply N.lt_irrefl in BC1.
          exfalso. apply BC1.
          (* X1 holds the index of the current char. *)
          split. psimpl; psimpl in ACC. assumption.
          (* X2 holds the digit value of the current char. *)
          split. psimpl. rewrite BC2. unfold digit_value. psimpl. rewrite MEM in *. rewrite BC2.
          reflexivity.
          (* X4 is 10 (the multiplier). *)
          split. psimpl; assumption.
          (* MEM *)
          psimpl; assumption.
        (* The current char is a digit between 0-8 *)
        destruct BC as (BC1 & BC2). apply N.eqb_neq in BC2. exists j, k, j. unfold inv_digit_multiply.
          (* digit_start *)
          split. digit_start_persists DSTART.
          (* all_digits *)
          split. assumption.
          (* Prove the current digit is in fact a digit, because we're in the loop. *)
          rewrite MEM in *. apply N.leb_gt in BC1. apply msub_lt_9 in BC1.
          destruct BC1 as (GE48 & LT57).
          split. unfold is_digit; split; rewrite <- ACC.
            assumption.
            apply N.lt_le_incl. assumption.
          (* X1 holds the index of the current char. *)
          split. psimpl; psimpl in ACC. assumption.
          (* X2 holds the digit value of the current char. *)
          split. psimpl. unfold digit_value. psimpl. apply msub_mod_irrelevant. split; assumption.
          (* X4 is 10 (the multiplier). *)
          split. psimpl; assumption.
          (* MEM *)
          psimpl; assumption.

    (* 1048680 -> EXIT *)
    (* Case 1: Number is negative so cbnz branches *)
    step. intros. specialize PRE with (i:=i). destruct PRE; destruct H. rename x into j; rename x0 into k.
    unfold inv_post_digit_loop in H. destruct H as (DSTART & ALLD & NOND & MEM). exists j, k.
    unfold inv_postcondition. 
      split; try assumption.
      split; assumption.
    (* Case 2: Number is positive so cbnz does not branch *)
    step. intros. specialize PRE with (i:=i). destruct PRE; destruct H. rename x into j; rename x0 into k.
    unfold inv_post_digit_loop in H. destruct H as (DSTART & ALLD & NOND & MEM). exists j, k.
    unfold inv_postcondition. 
      split; try assumption.
      split; assumption.
Admitted.