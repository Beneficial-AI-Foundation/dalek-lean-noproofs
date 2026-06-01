/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.ExternallyVerified
import Curve25519Dalek.Math.Montgomery.Curve
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.EDWARDS_D2
import Curve25519Dalek.Aux

/-! # Spec Theorem for `EdwardsPoint::as_projective_niels`

Specification and proof for `EdwardsPoint::as_projective_niels`.

This function converts an EdwardsPoint to a ProjectiveNielsPoint, which is a
representation optimized for point addition operations.

Source: curve25519-dalek/src/edwards.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519_dalek.backend.serial.u64.field.FieldElement51
  curve25519_dalek.backend.serial.u64.constants
open curve25519_dalek.backend.serial.curve_models.ProjectiveNielsPoint
open curve25519_dalek.montgomery
namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Converts an EdwardsPoint from extended twisted Edwards coordinates (X, Y, Z, T)
to ProjectiveNiels coordinates (A, B, Z', C), where:
  - A ≡ Y + X (mod p)
  - B ≡ Y - X (mod p)
  - Z' = Z (unchanged)
  - C ≡ T * 2 * d (mod p)

natural language specs:

• The function always succeeds (no panic)
• For the input Edwards point (X, Y, Z, T), the resulting ProjectiveNielsPoint has coordinates:
  - A ≡ Y + X (mod p)
  - B ≡ Y - X (mod p)
  - Z' = Z
  - C ≡ T * 2 * d (mod p)
where p = 2^255 - 19
-/

/-- **Spec and proof concerning `edwards.EdwardsPoint.as_projective_niels`**:
- No panic (always returns successfully)
- For the input Edwards point (X, Y, Z, T), the resulting ProjectiveNielsPoint has coordinates:
  - A ≡ Y + X (mod p)
  - B ≡ Y - X (mod p)
  - Z' = Z
  - C ≡ T * 2 * d (mod p)
where p = 2^255 - 19
-/
@[externally_verified, progress]
theorem as_projective_niels_spec (e : EdwardsPoint)
    (he : e.IsValid) :
    as_projective_niels e ⦃ (pn : backend.serial.curve_models.ProjectiveNielsPoint) =>
      let X := Field51_as_Nat e.X
      let Y := Field51_as_Nat e.Y
      let Z := Field51_as_Nat e.Z
      let T := Field51_as_Nat e.T
      let A := Field51_as_Nat pn.Y_plus_X
      let B := Field51_as_Nat pn.Y_minus_X
      let Z' := Field51_as_Nat pn.Z
      let C := Field51_as_Nat pn.T2d
      A % p = (Y + X) % p ∧
      (B + X) % p = Y % p ∧
      Z' % p = Z % p ∧
      C % p = (T * (2 * d)) % p ∧
      (∀ i < 5, (pn.Y_plus_X[i]!).val < 2 ^ 54 ∧
      ∀ i < 5, (pn.Y_minus_X[i]!).val < 2 ^ 52 ∧
      ∀ i < 5, (pn.Z[i]!).val < 2 ^ 53 ∧
      ∀ i < 5, (pn.T2d[i]!).val < 2 ^ 52) ∧
      pn.IsValid ∧
      e.toPoint = pn.toPoint
       ⦄ := by
  sorry
end curve25519_dalek.edwards.EdwardsPoint
