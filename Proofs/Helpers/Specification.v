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


