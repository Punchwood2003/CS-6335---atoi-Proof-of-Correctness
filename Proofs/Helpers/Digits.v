(* Digit parsing and value computation for atoi *)

Require Import Picinae_armv8_pcode.
Require Import Utf8.
Require Import NArith.
Require Import ZArith.
Require Import Lia.
Import ARM8Notations.

Open Scope N.
Definition digit (n:nat) : Prop :=
  Nat.le n 9.
  
Open Scope N. 
Fixpoint handle_digits (mem:memory) (p:addr) (k:nat) (val:nat) :=
  match k with
  | O => O (* return 0 when no digits *)
  | S k' =>
    match mem Ⓑ[p] with
    | digit => handle_digits mem (p+1) k' (val*10 + N.to_nat(mem Ⓑ[p]))
    end
  end.
