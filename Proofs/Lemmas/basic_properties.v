(* Basic properties and lemmas for atoi proof *)

Require Import Picinae_armv8_pcode.
Require Import NArith.
Require Import Lia.

Open Scope N.

(* 
  This file does not need to exist as is, but is here for reference 
  as to how to create seperate lemma files under this project organization.
*)

(* Test lemma to verify imports are working *)
Lemma test_import : forall (x : N), x = x.
Proof. intros x. reflexivity. Qed.

