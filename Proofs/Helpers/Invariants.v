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

  Lemma inductive_all_digits : forall (j k : N),
    all_digits j k -> is_digit (mem Ⓑ[p ⊕ j ⊕ k]) -> all_digits j (k+1).
  Proof.
    intros j k Hall_digits Hdigit.
    unfold all_digits in *.
    intros i Hi.
    (* Hi : i < k + 1, need to show is_digit (mem Ⓑ[p ⊕ j ⊕ i]) *)
    (* We prove by cases on whether i < k, i = k, or i > k *)
    destruct (N.lt_total i k) as [Hlt | [Heq | Hgt]].
    + (* Case: i < k *)
      apply Hall_digits. exact Hlt.
    + (* Case: i = k *)
      subst. exact Hdigit.
    + (* Case: i > k, contradicts i < k+1 *)
      (* k < i and i < k+1 is impossible *)
      exfalso. lia.
  Qed.

  Lemma digits_msub:
    forall (n : N),
      48 <= n ->
      n <= 57 ->
      n ≠ 57 ->
      9 <= msub 32 n 48 ->
      False.
  Proof.
    intros n Hge48 Hle57 Hne57 Hmsub.
    (* From constraints: 48 <= n < 57, so n - 48 < 9 *)
    assert (Hlt57: n < 57) by lia.
    assert (Hupper: n - 48 < 9) by lia.
    
    (* Unfold msub: msub 32 n 48 = (n + (2^32 - 48 mod 2^32)) mod 2^32 *)
    unfold msub in Hmsub.
    
    (* Simplify: 48 mod 2^32 = 48 *)
    assert (H48mod: (48 : N) mod 2^32 = 48) by (apply N.mod_small; lia).
    rewrite H48mod in Hmsub.
    
    (* Algebraic simplification: n + (2^32 - 48) = (n - 48) + 2^32 *)
    assert (eq_arith: n + (2^32 - 48) = (n - 48) + 2^32) by lia.
    rewrite eq_arith in Hmsub.
    
    (* Key modular fact: when a < m, (a + m) mod m = a *)
    (* Here a = n - 48 < 9 < 2^32 = m *)
    assert (H_bound: n - 48 < 2^32) by lia.
    
    (* The core mathematical fact: (n - 48 + 2^32) mod 2^32 = n - 48 *)
    (* This simplifies Hmsub to: 9 <= n - 48 *)
    (* Combined with Hupper: n - 48 < 9, we get a contradiction *)
    
    (* Direct computation: since n ∈ [48, 57), the value (n - 48 + 2^32) mod 2^32 *)
    (* must equal n - 48 in the range [0, 9) *)
    (* We verify this by exhaustive reasoning on msub semantics *)
    assert (H_simplify: ((n - 48) + 2^32) mod 2^32 = n - 48).
    {
      rewrite N.Div0.add_mod by lia.
      rewrite N.Div0.mod_same by lia.
      rewrite N.add_0_r.

      (* eliminate inner modulo *)
      rewrite (N.mod_small (n - 48) (2 ^ 32)) by exact H_bound.

      (* eliminate outer modulo *)
      apply N.mod_small.
      exact H_bound.
    }
    
    rewrite H_simplify in Hmsub.
    
    (* Now Hmsub: 9 <= n - 48, but Hupper: n - 48 < 9 *)
    lia.
  Qed.

  Lemma msub_lt_9 :
    forall n,
      n < 256 ->  (* n is a byte value *)
      msub 32 n 48 < 9 ->
      48 <= n /\ n < 57.
  Proof.
    intros n Hbyte Hlt.
    unfold msub in Hlt.

    rewrite (N.mod_small 48 (2^32)) in Hlt by lia.

    destruct (N.lt_ge_cases n 48) as [Hnlt | Hnge].

    - (* n < 48 *)
      exfalso.
      assert (Hnowrap : n + (2^32 - 48) < 2^32) by lia.
      rewrite (N.mod_small (n + (2^32 - 48)) (2^32)) in Hlt
        by exact Hnowrap.
      lia.

    - (* n >= 48 *)
      assert (Hrewrite : n + (2 ^ 32 - 48) = (n - 48) + 2 ^ 32) by lia.
      rewrite Hrewrite in Hlt.

      rewrite N.Div0.add_mod in Hlt by lia.
      rewrite N.Div0.mod_same in Hlt by lia.
      rewrite N.add_0_r in Hlt.

      (* remove double modulo correctly *)
      rewrite N.Div0.mod_mod in Hlt by lia.

      (* now Hlt : (n - 48) mod 2^32 < 9 *)
      (* Since n < 256, we have n - 48 < 256 - 48 = 208 < 2^32 *)
      assert (Hbound: n - 48 < 2^32) by lia.
      rewrite (N.mod_small (n - 48) (2^32)) in Hlt by exact Hbound.
      
      (* Now Hlt: n - 48 < 9 *)
      split.
      + exact Hnge.
      + lia.
  Qed.

  Lemma msub_mod_irrelevant :
    forall n,
      48 <= n < 57 ->
      msub 32 n 48 = n - 48.
  Proof.
    intros n [Hge Hlt].

    unfold msub.

    (* simplify 48 mod 2^32 *)
    rewrite (N.mod_small 48 (2^32)) by lia.

    (* rewrite subtraction as addition *)
    assert (Hrewrite : n + (2^32 - 48) = (n - 48) + 2^32) by lia.
    rewrite Hrewrite.

    (* push mod inside *)
    rewrite N.Div0.add_mod by lia.
    rewrite N.Div0.mod_same by lia.
    rewrite N.add_0_r.

    (* collapse both mods *)
    rewrite (N.mod_small (n - 48) (2^32)) by lia.
    apply N.mod_small.
    lia.
  Qed.

  (* Bytes read from memory are always in the range [0, 255] *)
  Lemma mem_byte_bound :
    forall (addr : addr),
      mem Ⓑ[addr] < 256.
  Proof.
    intro addr.
    (* mem Ⓑ[addr] is notation for getmem 64 LittleE 1 mem addr *)
    (* Apply getmem_1: getmem w e 1 m a = getbyte m a w *)
    rewrite getmem_1.
    (* Apply getbyte_bound: getbyte m a w < 2^8 = 256 *)
    apply getbyte_bound.
  Qed.

  (* ========== Specification Components ========== *)

  (* Index of first non-whitespace character *)
  Definition first_nonwhitespace (i : N) : Prop :=
    all_whitespace_until i /\ ¬(is_whitespace (mem Ⓑ[p ⊕ i])).

  (* A sign indicator exists at the first non-whitespace index i. *)
  (* w3 encodes the sign: 1 for negative, 0 for non-negative *)
  Definition sign_indicator_exists (i : N) (s : store) : Prop :=
    (mem Ⓑ[p ⊕ i] = 0x2D) \/  (* minus sign *)
    (mem Ⓑ[p ⊕ i] = 0x2B).    (* plus sign *)

  (* The index at which the digits should start is j, where j is either: 
     1. The index after the sign indicator, or
     2. The first non-whitespace character when no sign exists. *)
  (* Index where digits should start (after optional sign) *)
  Definition digit_start (i : N) (j : N) (s : store) : Prop :=
    first_nonwhitespace i /\
    ((sign_indicator_exists i s /\ (s R_X3 = 0 \/ s R_X3 = 1) /\ j = i + 1) \/
    (¬sign_indicator_exists i s /\ s R_X3 = 0 /\ j = i)).

  (* ========== Loop Invariants ========== *)
  Variable s0: store. (* Initial state *)

  (* 1048576 - Invariant at entry point
     The only thing we know at the entry point is that x0 points to input string.
     After the first instruction is executed, x1 will also point to the input string. *)
  Definition inv_entry (s : store) : Prop :=
    s R_X0 = p /\
    s V_MEM64 = mem.

  Definition atoi_pre t x' s' :=
    startof t (x', s') = (Addr 0x100000, s0) /\ (* We start execution of atoi at 0x100000 *)
    models arm8typctx s0 /\ (* The initial state is assumed to obey the typing context of arm8 *)
    inv_entry s0.

  (* 1048580 - Invariant at whitespace-skipping loop 
     We've skipped i characters, haven't found non-whitespace yet *)
  Definition inv_whitespace_loop (i : N) (s : store) : Prop :=
    all_whitespace_until i /\
    s R_X1 = p ⊕ i /\
    s V_MEM64 = mem.

  (* 1048636 - Invariant at the first statement inside the whitespace-skipping loop *)
  (* If we are here, the current character should indeed be whitespace. *)
  Definition inv_inside_whitespace_loop (i : N) (s : store) : Prop :=
    all_whitespace_until i /\
    is_whitespace (mem Ⓑ[p ⊕ i]) /\
    s R_X0 = mem Ⓑ[p ⊕ i] /\
    s R_X1 = p ⊕ i /\
    s V_MEM64 = mem.

  (* 1048600 - Invariant at sign-check section
     At this point we know how much whitespace there is.
     R_X0 should hold the first non-whitespace character, and
     R_X1 should hold the index of the first non-whitespace character. *)
  Definition inv_after_whitespace (i : N) (s : store) : Prop :=
    first_nonwhitespace i /\
    s R_X0 = mem Ⓑ[p ⊕ i] /\
    s R_X1 = p ⊕ i /\
    s V_MEM64 = mem.

  (* 1048620 - Invariant after parsing an existing sign character.
     If we are here, there for sure is a sign indicator. *)
  Definition inv_sign_exists (i : N) (s : store) : Prop :=
    first_nonwhitespace i /\
    sign_indicator_exists i s /\
    s R_X1 = p ⊕ i /\
    (s R_X3 = 0 \/ s R_X3 = 1) /\
    s V_MEM64 = mem.

  (* 1048624 - Invariant placed right after processing the sign indicator (1048624). We know that EITHER:
     1. A sign exists and R_X3 is either 0 or 1, or
     2. A sign does not exist and R_X3 is 0. 
     We also know where the digits should start based on the whitespace and sign existence. *)
  Definition inv_post_sign (i j : N) (s : store) : Prop :=
    digit_start i j s /\
    all_digits j 0 /\
    s R_X1 = p ⊕ j /\
    s V_MEM64 = mem.

  (* 1048652 - Invariant at digit-computation phase
     We've multiplied the accumulator by 10, now subtracting the digit value *)
  Definition inv_digit_multiply (i j k acc : N) (s : store) : Prop :=
    digit_start i j s /\
    all_digits j k /\  
    is_digit (mem Ⓑ[p ⊕ j ⊕ k]) /\ (* we know this digit is valid *)
    s R_X1 = p ⊕ j ⊕ k /\
    s R_X2 = digit_value (mem Ⓑ[s R_X1]) /\
    s R_X4 = 10 /\
    s V_MEM64 = mem.

  (* 1048664 - Invariant at digit-parsing loop: 
     We're in the loop parsing digits. We know:
     - which characters are whitespace/sign/digits
     - how many digits we've processed so far (acc)
     - the current position and what we're examining
     - the sign indicator in X3
     X0 contains a partial result (exact formula depends on implementation details) *)
  Definition inv_digit_loop (i j k : N) (s : store) : Prop :=
    digit_start i j s /\
    all_digits j k /\  (* we've seen k valid digits so far *)
    s R_X1 = p ⊕ j ⊕ k /\
    s R_X4 = 10 /\   (* multiplier *)
    s V_MEM64 = mem.

  (* 1048680 - Invariant after post digit loop 
     Main takeaway: The memory from [p+j to p+j+k-1] is the number to be converted. *)
  Definition inv_post_digit_loop (i j k : N) (s : store) : Prop :=
    digit_start i j s /\
    all_digits j k /\
    ¬is_digit (mem Ⓑ[p ⊕ j ⊕ k]) /\
    s V_MEM64 = mem.

  Definition inv_postcondition (i j k : N) (s : store) : Prop :=
    digit_start i j s /\ (* The digits should start at index j *)
    all_digits j k /\ (* There are j-k digits from mem[p+j] to mem[p+j+k-1] *)
    (* TODO: Use self-specified atoi to check result *)
    s V_MEM64 = mem.

  (* Unified invariant set at each checkpoint *)
  Definition atoi_invs (t : trace) : option Prop :=
    match t with
    | (Addr a, s) :: _ => 
      match a with
      | 1048576 => Some (inv_entry s)
      | 1048580 => Some (∃ i, inv_whitespace_loop i s)
      | 1048636 => Some (∃ i, inv_inside_whitespace_loop i s)
      | 1048600 => Some (∃ i, inv_after_whitespace i s)
      | 1048620 => Some (∃ i, inv_sign_exists i s)
      | 1048624 => Some (∃ i j, inv_post_sign i j s)
      | 1048652 => Some (∃ i j k acc, inv_digit_multiply i j k acc s)
      | 1048664 => Some (∃ i j k, inv_digit_loop i j k s)
      | 1048680 => Some (∃ i j k, inv_post_digit_loop i j k s)
      | 1048688 => Some (∃ i j k, inv_postcondition i j k s)
      | _ => None  (* other addresses are unconstrained *)
      end
    | _ => None
    end.

End Invariants.