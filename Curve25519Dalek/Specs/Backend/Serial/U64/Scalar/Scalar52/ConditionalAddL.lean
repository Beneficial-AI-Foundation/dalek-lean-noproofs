/-
Copyright 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.L

/-! # Spec Theorem for `Scalar52::conditional_add_l`

Specification and proof for `Scalar52::conditional_add_l`.

This function conditionally adds the group order L to a scalar based on a choice parameter.

Source: curve25519-dalek/src/backend/serial/u64/scalar.rs -/

attribute [-simp] Int.reducePow Nat.reducePow
set_option exponentiation.threshold 260

/-! # Spec Theorem for `Scalar52::conditional_add_l`

This function conditionally adds the group order `L` to a scalar based on a `choice` parameter.

Source: curve25519-dalek/src/backend/serial/u64/scalar.rs

## Rust source

```rust
pub(crate) fn conditional_add_l(&mut self, condition: Choice) -> u64 {
    let mut carry: u64 = 0;
    let mask = (1u64 << 52) - 1;

    let mut i = 0;
    while i < 5 {
        let addend = u64::conditional_select(&0, &constants::L[i], condition);
        carry = (carry >> 52) + self[i] + addend;
        self[i] = carry & mask;
        i += 1;
    }

    carry
}
```

## Proof overview

The function iterates over 5 limbs, at each step computing:

```rust
carry' = (carry >> 52) + self[i] + addend
self[i] = carry' & mask
```

where `addend = L[i]` if `condition=1` or `0` otherwise, and `mask = 2^52 - 1`.

**No overflow**: The key invariant is `carry < 2^53` at each iteration.
This follows from the precondition `self[i] < 2^52` and the fact that `L[i] < 2^52`:
  `carry >> 52 < 2`  (since carry < 2^53)
  `self[i]     < 2^52`
  `addend      ≤ L[i] < 2^52`
  `total       < 2 + 2^52 + 2^52 < 2^53 < 2^64`
Without the bound `self[i] < 2^52`, the addition could overflow u64.

**Value invariant**: After processing limb i, the loop maintains:
```
  Scalar52_as_Nat(self') + 2^(52*(i+1)) * (carry'/2^52)
    = Scalar52_as_Nat(self_orig) + condition * Σ_{j < i+1} 2^(52*j) * L[j]
         + 2^(52*0) * (carry_init/2^52)
```
This follows from the standard radix-2^52 addition with carry propagation:
each `self[i] = carry' mod 2^52` stores the low bits, while `carry'/2^52`
propagates to the next limb.

After all 5 limbs, the full sum telescopes to:
```
  Scalar52_as_Nat(result) + 2^260 * (carry_final/2^52)
    = Scalar52_as_Nat(self) + condition * Scalar52_as_Nat(L)
```

**Natural language spec**:

    • Input: limbs bounded by 2^52
    • If condition is 1 and input ∈ [2^260 - L, 2^260):
        - Output value: u' + 2^260 = u + L
        - Output canonical: u' < L
        - Output limbs: < 2^52
    • If condition is 0:
        - Output value: u' = u
        - Output limbs: < 2^52
    • Carry value: not used by caller

-/

namespace curve25519_dalek
open Aeneas Aeneas.Std Aeneas.Std.WP Result

/- Replace the spec currently in FunsExternal.lean with an alternative phrased in terms of
`Choice.one`/`Choice.zero`.
TODO: make this change throughout the code or revert this. -/

attribute [-progress] U64.Insts.SubtleConditionallySelectable.conditional_select_spec
/-- Progress spec for U64.Insts.SubtleConditionallySelectable.conditional_select -/
@[progress]
theorem U64.Insts.SubtleConditionallySelectable.conditional_select_spec' (a b : U64) (choice : subtle.Choice) :
    U64.Insts.SubtleConditionallySelectable.conditional_select a b choice ⦃ (res : U64) =>
      (choice = Choice.one → res = b) ∧
      (choice = Choice.zero → res = a) ⦄ := by
  sorry
end curve25519_dalek

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

@[progress]
theorem conditional_add_l_loop_spec (self : Scalar52) (condition : subtle.Choice)
    (carry : U64) (mask : U64) (i : Usize) (hself : ∀ j < 5, self[j]!.val < 2 ^ 52)
    (hmask : mask.val = 2 ^ 52 - 1) (hi : i.val ≤ 5) (hcarry : carry.val < 2 ^ 53) :
    conditional_add_l_loop self condition carry mask i ⦃ (result : U64 × Scalar52) =>
      (∀ j < 5, result.2[j]!.val < 2 ^ 52) ∧
      (Scalar52_as_Nat result.2 + 2 ^ 260 * (result.1.val / 2 ^ 52) =
        Scalar52_as_Nat self + (if condition = Choice.one then Scalar52_as_Nat constants.L else 0) +
        2 ^ (52 * i.val) * (carry.val / 2 ^ 52) -
        (if condition = Choice.one then ∑ j ∈ Finset.Ico 0 i.val, 2 ^ (52 * j) * constants.L[j]!.val
          else 0)) ⦄ := by
  sorry
/-- **Spec for `scalar.Scalar52.conditional_add_l`** (tailored for use in `sub`):
- Requires input limbs bounded by 2^52
- When condition is 1, requires input value in [2^260 - L, 2^260)
- When condition is 1: result + 2^260 = input + L, with result < L and limbs < 2^52
- When condition is 0: result unchanged with limbs < 2^52
-/
@[progress]
theorem conditional_add_l_spec (self : Scalar52) (condition : subtle.Choice)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 52)
    (hself' : condition = Choice.one → 2 ^ 260 ≤ Scalar52_as_Nat self + L)
    (hself'' : condition = Choice.one → Scalar52_as_Nat self < 2 ^ 260)
    (hself''' : condition = Choice.zero → Scalar52_as_Nat self < L) :
    conditional_add_l self condition ⦃ (result : U64 × Scalar52) =>
      (∀ i < 5, result.2[i]!.val < 2 ^ 52) ∧
      (Scalar52_as_Nat result.2 < L) ∧
      (condition = Choice.one → Scalar52_as_Nat result.2 + 2 ^ 260 = Scalar52_as_Nat self + L) ∧
      (condition = Choice.zero → Scalar52_as_Nat result.2 = Scalar52_as_Nat self) ⦄ := by
  sorry
end curve25519_dalek.backend.serial.u64.scalar.Scalar52
