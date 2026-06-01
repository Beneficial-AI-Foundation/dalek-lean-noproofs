/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jinxing Lim
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MulInternal
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryReduce
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.RR

/-! # Spec Theorem for `Scalar52::mul`

This function performs regular scalar multiplication (not Montgomery multiplication).

Source: curve25519-dalek/src/backend/serial/u64/scalar.rs

-/

open Aeneas Aeneas.Std Aeneas.Std.WP Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option exponentiation.threshold 262

/-
natural language description:

    • Takes two input scalars a and b (not in Montgomery form) and returns
      a scalar representing their product modulo L.

    • The implementation works by:
      1. Computing mul_internal(a, b) to get the polynomial product
      2. Applying montgomery_reduce to get ab * R^(-1) (in Montgomery form)
      3. Multiplying by RR (which is R^2 mod L) via mul_internal
      4. Applying montgomery_reduce again to convert back to normal form

    • The double Montgomery reduction with RR effectively computes:
      ((a * b * R^(-1)) * R^2 * R^(-1)) = a * b (mod L)

natural language specs:

    • For any two scalars a and b:
      - The function returns successfully
      - Scalar52_as_Nat(result) ≡ Scalar52_as_Nat(a) * Scalar52_as_Nat(b) (mod L)
      - Each limb of the result is bounded by 2^52
-/

/-- **Spec theorem for `scalar.Scalar52.mul`**:
- The result represents the product of the two input scalars modulo L
- Input scalars should have limbs bounded by 2^62 (standard Scalar52 representation)
- Output limbs are bounded by 2^52 -/
@[progress]
theorem mul_spec (a b : Scalar52)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 62) (hb : ∀ i < 5, b[i]!.val < 2 ^ 62) :
    mul a b ⦃ ( result : Scalar52 ) =>
      Scalar52_as_Nat result ≡ Scalar52_as_Nat a * Scalar52_as_Nat b [MOD L] ∧
      Scalar52_as_Nat result < L ∧ ∀ i < 5, result[i]!.val < 2 ^ 52 ⦄ := by
  sorry
end curve25519_dalek.backend.serial.u64.scalar.Scalar52
