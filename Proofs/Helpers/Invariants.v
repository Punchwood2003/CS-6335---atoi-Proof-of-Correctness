(* Loop invariants for the binary atoi implementation *)

Require Import Picinae_armv8_pcode.
Require Import Utf8.
Require Import NArith.
Require Import ZArith.
Require Import Lia.
Require Import Whitespace.
Require Import Sign.
Require Import Digits.
Require Import BitWidth.
Require Import Specification.
Import ARM8Notations.

Open Scope N.

Section Invariants.

  Variable mem : memory.
  Variable p : addr.

  (* ========== Helper Predicates ========== *)

  (* All bytes from index 0 to i-1 are whitespace, or i = 0. *)
  Definition all_whitespace_until (i : N) : Prop :=
    is_whitespace (mem Ⓑ[p ⊕ i ⊖ 1]) \/ i = 0.

  (* All bytes from index j to j⊕k-1 are digits *)
  Definition all_digits (j k : N) : Prop :=
    ∀ i, i < k -> is_digit (mem Ⓑ[p ⊕ j ⊕ i]).

  (* ========== Specification Components ========== *)

  (* Index of first non-whitespace character *)
  Definition first_nonwhitespace (i : N) : Prop :=
    all_whitespace_until i /\ ¬(is_whitespace (mem Ⓑ[p ⊕ i])).

  (* w3 encodes the sign: 1 for negative, 0 for non-negative *)
  Definition sign_indicator_exists (i : N) (s : store) : Prop :=
    (mem Ⓑ[p ⊕ i] = 0x2D /\ s R_X3 = 1) \/  (* minus sign *)
    (mem Ⓑ[p ⊕ i] = 0x2B /\ s R_X3 = 0).    (* plus sign *)

  (* Index where digits should start (after optional sign) *)
  Definition digit_start (i : N) (j : N) (s : store) : Prop :=
    (sign_indicator_exists i s /\ j = i + 1) \/
    (¬sign_indicator_exists i s /\ j = i).

  (* ========== Loop Invariants ========== *)
  Variable s0: store. (* Initial state *)

  (* 1048576 - Invariant at entry point
     The only thing we know at the entry point is that x0 points to input string.
     After the first instruction is executed, x1 will also point to the input string. *)
  Definition inv_entry (s : store) : Prop :=
    s R_X0 = p.

  Definition atoi_pre t x' s' :=
    startof t (x', s') = (Addr 0x100000, s0) /\ (* We start execution of atoi at 0x100000 *)
    models arm8typctx s0 /\ (* The initial state is assumed to obey the typing context of arm8 *)
    inv_entry s0.

  (* 1048580 - Invariant at whitespace-skipping loop 
     We've skipped i characters, haven't found non-whitespace yet *)
  Definition inv_whitespace_loop (i : N) (s : store) : Prop :=
    all_whitespace_until i /\
    s R_X1 = p ⊕ i.

  (* 1048636 - Invariant at the first statement inside the whitespace-skipping loop *)
  (* If we are here, the current character should indeed be whitespace. *)
  Definition inv_inside_whitespace_loop (i : N) (s : store) : Prop :=
    is_whitespace (mem Ⓑ[p ⊕ i]) /\
    s R_X0 = mem Ⓑ[p ⊕ i] /\
    s R_X1 = p ⊕ i.

  (* 1048600 - Invariant at sign-check section
     At this point we know how much whitespace there is.
     R_X0 should hold the first non-whitespace character, and
     R_X1 should hold the index of the first non-whitespace character. *)
  Definition inv_after_whitespace (i : N) (s : store) : Prop :=
    first_nonwhitespace i /\
    s R_X0 = mem Ⓑ[p ⊕ i] /\
    s R_X1 = p ⊕ i.

  (* 1048620 - Invariant after parsing an existing sign character.
     If we are here, there for sure is a sign indicator.\
     Therefore, we know the index at which digits should start appearing. *)
  Definition inv_sign_exists (i j : N) (s : store) : Prop :=
    sign_indicator_exists i s /\
    digit_start i j s /\
    s R_X1 = p ⊕ i.

  (* 1048624 - Invariant placed right after processing the sign indicator (1048624). We know that EITHER:
     1. A sign exists and R_X3 is either 0 or 1, or
     2. A sign does not exist and R_X3 is 0. 
     We also know where the digits should start based on the whitespace and sign existence. *)
  Definition inv_post_sign (i j : N) (s : store) : Prop :=
    ((sign_indicator_exists i s /\ (s R_X3 = 0 \/ s R_X3 = 1)) \/ 
    (¬(sign_indicator_exists i s) /\ s R_X3 = 0)) /\
    digit_start i j s /\
    s R_X1 = p ⊕ j.

  (* 1048652 - Invariant at digit-computation phase
     We've multiplied the accumulator by 10, now subtracting the digit value *)
  Definition inv_digit_multiply (i j k acc : N) (s : store) : Prop :=
    first_nonwhitespace i /\
    sign_indicator_exists i s /\
    digit_start i j s /\
    all_digits j (acc + 1) /\  (* we know this digit is valid *)
    acc < k /\
    s R_X1 = p ⊕ j ⊕ acc /\
    s R_X2 = digit_value (mem Ⓑ[s R_X1]) /\
    s R_X4 = 10.

  (* 1048664 - Invariant at digit-parsing loop: 
     We're in the loop parsing digits. We know:
     - which characters are whitespace/sign/digits
     - how many digits we've processed so far (acc)
     - the current position and what we're examining
     - the sign indicator in X3
     X0 contains a partial result (exact formula depends on implementation details) *)
  Definition inv_digit_loop (i j k acc : N) (s : store) : Prop :=
    inv_post_sign i j s /\
    all_digits j k /\  (* we've seen k valid digits so far *)
    acc <= k /\  (* acc is how many we've actually processed *)
    s R_X1 = p ⊕ j ⊕ acc /\
    s R_X4 = 10.   (* multiplier *)

  (* 1048688 (0x100070) - Exit postcondition
     At this point, R_X0 should contain the result that matches
     the Gallina specification atoi function.
     This connects the binary implementation to the trusted specification. *)
  Definition inv_exit (w d : nat) (s : store) : Prop :=
    Z.of_N (s R_X0) = atoi mem p w d.
  
  (* Unified invariant set at each checkpoint *)
  Definition atoi_invs (t : trace) : option Prop :=
    match t with
    | (Addr a, s) :: _ => 
      match a with
      | 1048576 => Some (inv_entry s)
      | 1048580 => Some (∃ i, inv_whitespace_loop i s)
      | 1048636 => Some (∀ i, inv_inside_whitespace_loop i s)
      | 1048600 => Some (∀ i, inv_after_whitespace i s)
      | 1048620 => Some (∀ i, ∃ j, inv_sign_exists i j s)
      | 1048624 => Some (∀ i, ∃ j, inv_post_sign i j s)
      | 1048652 => Some (∀ i k acc, ∃ j, inv_digit_multiply i j k acc s)
      | 1048664 => Some (∀ i, ∃ j k acc, inv_digit_loop i j k acc s)
      | 1048688 => Some (∃ w d, inv_exit w d s)
      | _ => None  (* other addresses are unconstrained *)
      end
    | _ => None
    end.

End Invariants.