(* Sign detection logic for atoi *)

(* Import standard libraries *)
Require Import ZArith.
Require Import Lia.

(* Import Picinae notations/tactics *)
Require Import Picinae_armv8_pcode.
Import ARM8Notations.

Open Scope Z.

(* 
  0x2D = 45 (* minus sign *)
  0x2B = 43 (* plus sign *) 
*)
  
(* if we have - then return -1 else 1 *)
Definition handle_sign (mem:memory) (p:addr) :=
  let x := Z.of_N(mem Ⓑ[p]) in
  if (Z.eq_dec x 45) then -1
  else 1.

(* if we have - or + then return p+1 else p *)
Close Scope Z.
Definition handle_sign_space (mem:memory) (p:addr) :=
  let x := Z.of_N(mem Ⓑ[p]) in
  if (Z.eq_dec x 45) then (p+(Z.to_N 1))
  else if (Z.eq_dec x 43) then (p+(Z.to_N 1))
  else p. 
