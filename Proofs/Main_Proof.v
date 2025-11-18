(* Main atoi proof - ties together lifted source and all lemmas *)

Require Import Picinae_armv8_pcode.
Require Import NArith.
Require Import Lia.
(* Import the Lifted Source file *)
Require Import atoi_lo_atoi_armv8.
(* Import all lemmas *)
Require Import basic_properties.

Open Scope N.

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
