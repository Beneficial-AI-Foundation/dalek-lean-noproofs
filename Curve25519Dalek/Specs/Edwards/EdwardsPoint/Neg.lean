/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg
import Curve25519Dalek.Math.Montgomery.Curve
/-! # Spec Theorem for `EdwardsPoint::neg`

Specification and proof for the `Neg` trait implementation for Edwards points.

This function negates an Edwards point via elliptic curve negation: it negates the
X and T coordinates while keeping Y and Z unchanged, which corresponds to negating
the x-coordinate in affine form.

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.edwards.EdwardsPoint
open curve25519_dalek.backend.serial.u64.field
namespace curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint

/-
natural language description:

• Takes an EdwardsPoint `self`
• Returns its negation as an EdwardsPoint via elliptic curve group negation
• Implementation: negates the X and T coordinates while keeping Y and Z unchanged

natural language specs:

• The function always succeeds (no panic) for valid input Edwards points
• The result is a valid Edwards point
• The result represents the negation of the input (in the context of elliptic curve negation)
-/

/-- **Spec and proof concerning `Shared0EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint.neg`**:
• The function always succeeds (no panic) for valid inputs
• The result is a valid Edwards point
• The result represents the negation of the input (in the context of elliptic curve negation)
-/
@[progress]
theorem neg_spec
    (self : edwards.EdwardsPoint)
    (h_self_valid : self.IsValid) :
    neg self ⦃ (result : edwards.EdwardsPoint) =>
      result.IsValid ∧
      result.toPoint = -self.toPoint ⦄ := by
  sorry
end curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithNegEdwardsPoint
