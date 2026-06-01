/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.SquareInternal
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MulInternal
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.MontgomeryReduce
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.RR

/-! # Spec Theorem for `Scalar52::square`

Specification and proof for `Scalar52::square`.

This function performs regular scalar squaring (not Montgomery squaring).

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

-/

open Aeneas Aeneas.Std Aeneas.Std.WP Result
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option exponentiation.threshold 262

/-
natural language description:

    • Takes an input scalar `self` (not in Montgomery form) and returns
      a scalar representing its square modulo L.

    • The implementation works by:
      1. Computing square_internal(self) to get the polynomial square
      2. Applying montgomery_reduce to get self² * R⁻¹ (in Montgomery form)
      3. Multiplying by RR (which is R² mod L) via mul_internal
      4. Applying montgomery_reduce again to convert back to normal form

    • The double Montgomery reduction with RR effectively computes:
      ((self² * R⁻¹) * R² * R⁻¹) = self² (mod L)

natural language specs:

    • For any scalar self:
      - The function returns successfully
      - Scalar52_as_Nat(result) ≡ Scalar52_as_Nat(self) * Scalar52_as_Nat(self) (mod L)
      - Each limb of the result is bounded by 2^52
-/

/- Helper lemmas/theorems -/

-- Helper theorem to cancel R [mod L] on right (same as in Mul.lean)
private theorem cancelR {a b : ℕ} (h : a * R ≡ b * R [MOD L]) : a ≡ b [MOD L] := by
  have hcoprime : Nat.Coprime R L := by
    unfold R L Nat.Coprime
    simp
  have h1 := Nat.Coprime.symm hcoprime
  exact Nat.ModEq.cancel_right_of_coprime h1 h

/- End of helper lemmas/theorems -/

/-- **Spec and proof concerning `scalar.Scalar52.square`**:
- No panic (always returns successfully)
- The result represents the square of the input scalar modulo L
- Input scalar should have limbs bounded by 2^62 (standard Scalar52 representation)
- Output limbs are bounded by 2^52
-/
@[progress]
theorem square_spec (self : Scalar52)
    (hself : ∀ i < 5, self[i]!.val < 2 ^ 62) :
    square self ⦃ ( result : Scalar52 ) =>
      Scalar52_as_Nat result ≡ Scalar52_as_Nat self * Scalar52_as_Nat self [MOD L] ∧
      ∀ i < 5, result[i]!.val < 2 ^ 52 ⦄ := by
  sorry
end curve25519_dalek.backend.serial.u64.scalar.Scalar52
