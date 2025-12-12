(* Whitespace detection and skipping logic for atoi *)

Require Import Picinae_armv8_pcode.
Require Import Utf8.
Require Import NArith.
Require Import ZArith.
Require Import Lia.
Import ARM8Notations.

Open Scope N.

(* (0x09 <= b /\ b <= 0x0d) \/ b = 0x20 *)
Inductive whitespace : N -> Prop :=
  | whitespace_tab  : whitespace 0x9
  | whitespace_lf   : whitespace 0xa
  | whitespace_vt   : whitespace 0xb
  | whitespace_ff   : whitespace 0xc
  | whitespace_cf   : whitespace 0xd
  | whitespace_dle  : whitespace 0x20.

Fixpoint handle_whitespace (mem:memory) (p:addr) (k:nat) :=
  match k with
  | O => p (* return the mem val where theres no more whitespace *)
  | S k' => 
    match mem Ⓑ[p] with
    | whitespace => handle_whitespace mem (p+1) k' (* move to next place *)
    end
  end.
