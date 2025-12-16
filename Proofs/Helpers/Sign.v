(* Sign detection logic for atoi *)

Require Import Picinae_armv8_pcode.
Require Import Utf8.
Require Import NArith.
Require Import ZArith.
Require Import Lia.
Require Import Whitespace.
Import ARM8Notations.

Open Scope Z.

(* 
  0x2D = 45 (* minus sign *)
  0x2B = 43 (* plus sign *) 
*)

Definition handle_sign (mem:memory) (p:addr) :=
  match Z.of_N(mem Ⓑ[p]) with 
  | 45 => -1 (* 0x2d as decimal, minus sign *)
  | 43 => 1 (* 0x2b as decimal, positive sign *)
  | _ => 1 (* no sign, positive value *)
  end.

Definition handle_sign_space (mem:memory) (p:addr): N :=
  match Z.of_N(mem Ⓑ[p]) with 
  | 45 => (p+(Z.to_N 1)) (* 0x2d as decimal, minus sign, move pointer by one *)
  | 43 => (p+(Z.to_N 1)) (* 0x2b as decimal, positive sign, move pointer by one *)
  | _ => p (* no sign, don't move pointer *)
  end. 
