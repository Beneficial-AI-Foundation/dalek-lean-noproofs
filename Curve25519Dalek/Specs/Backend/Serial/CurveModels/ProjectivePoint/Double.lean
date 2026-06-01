/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square2
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.AddAssign
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Math.Edwards.Curve
import Curve25519Dalek.Math.Edwards.Representation
import Mathlib.Data.ZMod.Basic

set_option linter.hashCommand false
#setup_aeneas_simps

/-! # Spec Theorem for `ProjectivePoint::double`

Specification and proof for `ProjectivePoint::double`.

This function implements point doubling on the Curve25519 elliptic curve using projective
coordinates. Given a point P = (X:Y:Z), it computes 2P (the point added to itself via
elliptic curve addition).

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithAddSharedAFieldElement51FieldElement51
open curve25519_dalek.Shared0FieldElement51.Insts.CoreOpsArithSubSharedAFieldElement51FieldElement51

namespace curve25519_dalek.backend.serial.curve_models.ProjectivePoint

/-
natural language description:

• Takes a ProjectivePoint with coordinates (X, Y, Z) and returns a CompletedPoint that results
from adding the input point to itself via elliptic curve point addition. Arithmetics are
performed in the field 𝔽_p where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic)
• Given input point (X, Y, Z), the output CompletedPoint (X', Y', Z', T') satisfies:
- X' ≡ 2XY (mod p)
- Y' ≡ Y² + X² (mod p)
- Z' ≡ Y² - X² (mod p)
- T' ≡ 2Z² - Y² + X² (mod p)
-/

/-- **Spec and proof concerning `backend.serial.curve_models.ProjectivePoint.double`**:
- No panic (always returns successfully)
- Given input ProjectivePoint with coordinates (X, Y, Z), the output CompletedPoint (X', Y', Z', T')
satisfies the point doubling formulas modulo p:
- X' ≡ 2XY (mod p)
- Y' ≡ Y² + X² (mod p)
- Z' ≡ Y² - X² (mod p)
- T' ≡ 2Z² - Y² + X² (mod p)
where p = 2^255 - 19
These formulas implement Edwards curve point doubling, computing P + P
(elliptic curve point addition) where P = (X:Y:Z).

Input bounds: X, Y limbs < 2^53 (for X + Y < 2^54), Z limbs < 2^54.
Output bounds: X', Z', T' limbs < 2^52, Y' limbs < 2^53.

TODO: Investigate if c.Y can achieve the tighter < 2^52 bound. Currently c.Y = YY + XX
where YY, XX < 2^52, giving Y < 2^53.
-/
@[progress]
theorem double_spec_aux (q : ProjectivePoint)
    (h_qX_bounds : ∀ i < 5, (q.X[i]!).val < 2 ^ 53)
    (h_qY_bounds : ∀ i < 5, (q.Y[i]!).val < 2 ^ 53)
    (h_qZ_bounds : ∀ i < 5, (q.Z[i]!).val < 2 ^ 54) :
    double q ⦃ c =>
    let X := Field51_as_Nat q.X
    let Y := Field51_as_Nat q.Y
    let Z := Field51_as_Nat q.Z
    let X' := Field51_as_Nat c.X
    let Y' := Field51_as_Nat c.Y
    let Z' := Field51_as_Nat c.Z
    let T' := Field51_as_Nat c.T
    X' % p = (2 * X * Y) % p ∧
    Y' % p = (Y^2 + X^2) % p ∧
    (Z' + X^2) % p = Y^2 % p ∧
    (T' + Z') % p = (2 * Z^2) % p ∧
    (∀ i < 5, c.X[i]!.val < 2 ^ 52) ∧
    (∀ i < 5, c.Y[i]!.val < 2 ^ 53) ∧
    (∀ i < 5, c.Z[i]!.val < 2 ^ 52) ∧
    (∀ i < 5, c.T[i]!.val < 2 ^ 52) ⦄ := by
  sorry
end curve25519_dalek.backend.serial.curve_models.ProjectivePoint

namespace curve25519_dalek.backend.serial.curve_models.ProjectivePoint

open Edwards
open curve25519_dalek.backend.serial.u64.field.FieldElement51
open curve25519_dalek.backend.serial.u64.field

private lemma double_lift_to_field_eqs (c : CompletedPoint) (q : ProjectivePoint)
    (hX_arith : Field51_as_Nat c.X % p = (2 * Field51_as_Nat q.X * Field51_as_Nat q.Y) % p)
    (hY_arith : Field51_as_Nat c.Y % p = (Field51_as_Nat q.Y ^ 2 + Field51_as_Nat q.X ^ 2) % p)
    (hZ_arith : (Field51_as_Nat c.Z + Field51_as_Nat q.X ^ 2) % p = Field51_as_Nat q.Y ^ 2 % p)
    (hT_arith : (Field51_as_Nat c.T + Field51_as_Nat c.Z) % p = (2 * Field51_as_Nat q.Z ^ 2) % p) :
    c.X.toField = 2 * q.X.toField * q.Y.toField ∧
    c.Y.toField = q.Y.toField ^ 2 + q.X.toField ^ 2 ∧
    c.Z.toField = q.Y.toField ^ 2 - q.X.toField ^ 2 ∧
    c.T.toField = 2 * q.Z.toField ^ 2 - c.Z.toField := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hX_arith; push_cast at h; exact h
  · unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hY_arith; push_cast at h; exact h
  · unfold FieldElement51.toField
    have h := lift_mod_eq _ _ hZ_arith; push_cast at h; exact eq_sub_of_add_eq h
  · unfold FieldElement51.toField at *
    have h := lift_mod_eq _ _ hT_arith; push_cast at h; exact eq_sub_of_add_eq h

attribute [local irreducible] p in
/--
Verification of the `double` function.
The theorem states that the Rust implementation of point doubling corresponds
exactly to the mathematical addition of the point to itself (`q + q`) on the Edwards curve.
-/
theorem double_spec
    (q : ProjectivePoint) (hq_valid : q.IsValid) :
    ∃ c, ProjectivePoint.double q = ok c ∧
    c.IsValid ∧ c.toPoint = q.toPoint + q.toPoint := by
  sorry
end curve25519_dalek.backend.serial.curve_models.ProjectivePoint
