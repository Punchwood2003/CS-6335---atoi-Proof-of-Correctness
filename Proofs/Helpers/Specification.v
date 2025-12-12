(* Complete atoi specification in Gallina
   This is the trusted implementation that defines what atoi should do *)

Require Import Picinae_armv8_pcode.
Require Import NArith.
Require Import ZArith.
Require Import Lia.
Require Import Whitespace.
Require Import Sign.
Require Import Digits.
Require Import BitWidth.
Import ARM8Notations.

Open Scope N.

Open Scope Z.
Definition atoi (mem:memory) (p:addr) (w:nat) (d:nat) :=
  let p_whitespace := handle_whitespace mem p w in
  let p_start := handle_sign_space mem p_whitespace in
  let sign := handle_sign mem p_whitespace in
  match handle_digits mem p_start d 0 with
  | O => 0
  | val => (sign * (Z.of_nat val))
  end.
