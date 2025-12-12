(* Bit width reasoning and overflow detection for atoi *)

Require Import Picinae_armv8_pcode.
Require Import Utf8.
Require Import NArith.
Require Import ZArith.
Require Import Lia.

Open Scope Z.

Section Invariants.
  Variable mem : memory.
  Variable p : addr.

  Definition bit_count_twos_complement (i : Z) : N :=
    match i with 
    | Z0 => 1
    | Z.pos n => N.succ (N.log2_up (N.succ (Npos n)))
    | Z.neg n => N.succ (N.log2_up (Npos n))
    end.

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
      rewrite N.pred_succ. simpl. split.
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

End Invariants.