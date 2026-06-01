/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Liao Zhang, Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes

/-! # Spec Theorem for `ProjectivePoint::as_affine`

Specification and proof for
`curve25519_dalek::montgomery::{curve25519_dalek::montgomery::ProjectivePoint}::as_affine`.

This function converts a projective point (U : W) to its affine u-coordinate
by computing U/W and encoding it as a 32-byte MontgomeryPoint.

**Note**: This is a pure encoding function that does not verify curve validity.

**Source**: curve25519-dalek/src/montgomery.rs, lines 330:4-333:5

-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Montgomery

namespace curve25519_dalek.montgomery.ProjectivePoint


/-
Natural language description:

• Computes the affine u-coordinate from projective point (U : W)
• Inverts W, multiplies U by W⁻¹, and encodes the result as 32 bytes
• Projective equivalence: (U : W) and (λU : λW) produce identical output

Natural language specs:

• The function always succeeds (no panic)
• Returns bytesToField(result) = U/W (mod p)
• Does not verify that the result represents a valid curve point
-/

lemma Field51_modP_ne_zero_of_toField_ne_zero
    (W : backend.serial.u64.field.FieldElement51)
    (hW : W.toField ≠ 0) :
    Field51_as_Nat W % p ≠ 0 := by
  sorry
/-- Division in ZMod p equals multiplication by inverse when we have modular multiplicative inverse. -/
lemma zmod_div_eq_mul_of_mod_inv (U W x_inv : Nat) (hW_ne : W % p ≠ 0) (h_inv : x_inv * W ≡ 1 [MOD p]) :
    (U : ZMod p) / (W : ZMod p) = (U : ZMod p) * (x_inv : ZMod p) := by
  sorry
/-- **Spec and proof concerning `montgomery.ProjectivePoint.as_affine`**:
- No panic (always returns successfully when input limbs satisfy bounds)
- Returns bytesToField(result) = U/W (mod p) where p = 2^255 - 19
- Does not verify curve validity (pure encoding of field element U/W)
-/
@[progress]
theorem as_affine_spec (self : montgomery.ProjectivePoint)
    (hU : self.U.IsValid)
    (hW : self.W.IsValid)
    (h_valid : self.W.toField ≠ 0) :
    as_affine self ⦃ res => (U8x32_as_Field res = self.U.toField  / self.W.toField) ∧
    (U8x32_as_Nat res < 2 ^255)  ⦄ := by
  sorry
end curve25519_dalek.montgomery.ProjectivePoint
