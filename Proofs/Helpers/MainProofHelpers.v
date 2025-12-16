(* Import standard libraries *)
Require Import Utf8.
Require Import ZArith.
Require Import Lia.

(* Import Picinae notations/tactics *)
Require Import Picinae_armv8_pcode.
Import ARM8Notations.

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


(* For bytes in whitespace range [9, 13) (excluding 13), msub 32 byte 9 < 4 *)
Lemma whitespace_msub_bound :
  forall n,
    n < 256 ->
    9 <= n < 13 ->
    msub 32 n 9 < 4.
Proof.
  intros n Hbyte [Hge Hlt].
  unfold msub.
  (* Simplify 9 mod 2^32 = 9 *)
  rewrite (N.mod_small 9 (2^32)) by (compute; trivial).
  (* Since 9 <= n < 256, we have n + (2^32 - 9) = (n - 9) + 2^32 *)
  assert (Hrewrite: n + (2^32 - 9) = (n - 9) + 2^32) by lia.
  rewrite Hrewrite.
  (* Simplify the modulo *)
  rewrite N.Div0.add_mod by lia.
  rewrite N.Div0.mod_same by lia.
  rewrite N.add_0_r.
  rewrite N.Div0.mod_mod by lia.
  (* Since n < 256, we have n - 9 < 247 < 2^32 *)
  rewrite (N.mod_small (n - 9) (2^32)) by lia.
  (* Now we have n - 9 < 4 since n < 13 *)
  lia.
Qed.

(* Converse: if msub 32 byte 9 < 4 for a byte, then byte is in [9, 13) *)
Lemma msub_lt_4_whitespace :
  forall n,
    n < 256 ->
    msub 32 n 9 < 4 ->
    9 <= n < 13.
Proof.
  intros n Hbyte Hmsub.
  unfold msub in Hmsub.
  rewrite (N.mod_small 9 (2^32)) in Hmsub by (compute; trivial).
  
  destruct (N.lt_ge_cases n 9) as [Hlt9|Hge9].
  - (* n < 9: derive contradiction *)
    (* When n < 9, n + (2^32 - 9) is large, close to 2^32 *)
    assert (Hsum_lt: n + (2^32 - 9) < 2^32) by lia.
    rewrite (N.mod_small (n + (2^32 - 9)) (2^32)) in Hmsub by lia.
    (* So we have 2^32 - 9 + n < 4 *)
    assert (Hcontra: 2^32 - 9 + n >= 2^32 - 9) by lia.
    assert (Hlarge: 2^32 - 9 > 4) by (compute; trivial).
    lia.
  - (* n >= 9: normal case *)
    assert (Hrewrite: n + (2^32 - 9) = (n - 9) + 2^32) by lia.
    rewrite Hrewrite in Hmsub.
    rewrite N.Div0.add_mod in Hmsub by lia.
    rewrite N.Div0.mod_same in Hmsub by lia.
    rewrite N.add_0_r in Hmsub.
    rewrite N.Div0.mod_mod in Hmsub by lia.
    assert (Hsmall: n - 9 < 2^32).
    { assert (H: 247 < 2^32) by (compute; trivial). lia. }
    rewrite (N.mod_small (n - 9) (2^32)) in Hmsub by lia.
    (* Now Hmsub: n - 9 < 4, so n < 13 *)
    split; lia.
Qed.

(* Helper lemma: If the bitwise OR of two conditions is positive,
    and we know the second condition is false, then the first must be true.
    Specialized for the whitespace BC0 condition structure. *)
Lemma whitespace_bc0_implies_msub :
  forall (byte : N) (bc0_val : N),
    (* BC0 structure: (if 4 <=? msub 32 byte 9 then 0 else 1) .| (if byte =? 13 then 1 else 0) *)
    bc0_val = (if 4 <=? msub 32 byte 9 then 0 else 1) .| (if byte =? 13 then 1 else 0) ->
    (* BC0 is positive *)
    (exists p_pos, bc0_val = N.pos p_pos) ->
    (* byte is not 13 *)
    byte ≠ 13 ->
    (* Then msub 32 byte 9 < 4 *)
    msub 32 byte 9 < 4.
Proof.
  intros byte bc0_val Hbc0 Hpos Hneq.
  destruct (N.ltb_spec (msub 32 byte 9) 4) as [Hlt|Hge].
  - (* Already have msub < 4 *)
    assumption.
  - (* Derive contradiction: if msub >= 4, then BC0 = 0 *)
    exfalso.
    destruct Hpos as [p_pos Hpos].
    rewrite Hpos in Hbc0.
    (* If msub >= 4, first part is 0 *)
    assert (Hleb: (4 <=? msub 32 byte 9) = true) by (apply N.leb_le; assumption).
    (* If byte ≠ 13, second part is 0 *)
    assert (Heqb: (byte =? 13) = false) by (apply N.eqb_neq; assumption).
    (* Substitute both *)
    rewrite Hleb, Heqb in Hbc0.
    (* Now we have N.pos p_pos = 0 .| 0 = 0, contradiction *)
    simpl in Hbc0. discriminate Hbc0.
Qed.