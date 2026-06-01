/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.CurveModels.CompletedPoint.Add




/- # Spec Theorem for `CompletedPoint::sub`

Specification and proof for `CompletedPoint::sub`.

This function implements the mixed subtraction of an AffineNielsPoint from an
Edwards point in extended coordinates, returning the result in completed
coordinates (ℙ¹ × ℙ¹). Given
- an EdwardsPoint P = (X:Y:Z:T) in extended ℙ³ coordinates (with X/Z = x, Y/Z = y, and T = XY/Z),
- an AffineNielsPoint N = (Y+X, Y−X, 2dXY),
it computes a CompletedPoint C = (X':Y':Z':T') corresponding to P − N.

The concrete formulas are:
- Y_plus_X  = Y + X
- Y_minus_X = Y − X
- PM        = Y_plus_X  · N.y_minus_x
- MP        = Y_minus_X · N.y_plus_x
- Txy2d     = T · N.xy2d
- Z2        = Z + Z
- X'        = PM − MP
- Y'        = PM + MP
- Z'        = Z2 − Txy2d
- T'        = Z2 + Txy2d

**Source**: curve25519-dalek/src/backend/serial/curve_models/mod.rs
-/


open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.curve_models

namespace curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAAffineNielsPointCompletedPoint



/-
natural language description:

• Takes an EdwardsPoint (X, Y, Z, T) in extended coordinates and an AffineNielsPoint
(Y+X, Y−X, 2dXY) and returns a CompletedPoint (X', Y', Z', T') in completed coordinates
(ℙ¹ × ℙ¹), representing the group subtraction P − N. Arithmetic is performed in the
field 𝔽_p where p = 2^255 - 19.

natural language specs:

• The function always succeeds (no panic)
• Given inputs P = (X, Y, Z, T) and N = (Y+X, Y−X, 2dXY), the output C = (X', Y', Z', T')
  satisfies modulo p:
  - X' ≡ ( (Y+X)·N.y_minus_x − (Y−X)·N.y_plus_x ) (mod p)
  - Y' ≡ ( (Y+X)·N.y_minus_x + (Y−X)·N.y_plus_x ) (mod p)
  - Z' ≡ ( 2·Z − T·N.xy2d ) (mod p)
  - T' ≡ ( 2·Z + T·N.xy2d ) (mod p)
-/


@[progress]
theorem sub_spec
  (self : edwards.EdwardsPoint)
  (other : backend.serial.curve_models.AffineNielsPoint)
  (h_selfX_bounds : ∀ i, i < 5 → (self.X[i]!).val < 2 ^ 53)
  (h_selfY_bounds : ∀ i, i < 5 → (self.Y[i]!).val < 2 ^ 53)
  (h_selfZ_bounds : ∀ i, i < 5 → (self.Z[i]!).val < 2 ^ 53)
  (h_selfT_bounds : ∀ i, i < 5 → (self.T[i]!).val < 2 ^ 53)
  (h_otherYpX_bounds : ∀ i, i < 5 → (other.y_plus_x[i]!).val < 2 ^ 53)
  (h_otherYmX_bounds : ∀ i, i < 5 → (other.y_minus_x[i]!).val < 2 ^ 53)
  (h_otherXY2d_bounds : ∀ i, i < 5 → (other.xy2d[i]!).val < 2 ^ 53) :
Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAAffineNielsPointCompletedPoint.sub self other ⦃ c =>
let X := Field51_as_Nat self.X
let Y := Field51_as_Nat self.Y
let Z := Field51_as_Nat self.Z
let T := Field51_as_Nat self.T
let YpX := Field51_as_Nat other.y_plus_x
let YmX := Field51_as_Nat other.y_minus_x
let XY2D := Field51_as_Nat other.xy2d
let X' := Field51_as_Nat c.X
let Y' := Field51_as_Nat c.Y
let Z' := Field51_as_Nat c.Z
let T' := Field51_as_Nat c.T
(X' + Y * YpX) % p = (((Y + X) * YmX) + X * YpX) % p ∧
(Y' + X * YpX) % p = (((Y + X) * YmX) + Y  * YpX) % p ∧
(Z' + (T * XY2D)) % p = (2 * Z) % p ∧
T' % p = ((2 * Z) + (T * XY2D)) % p ⦄
:= by
  sorry
end curve25519_dalek.Shared0EdwardsPoint.Insts.CoreOpsArithSubSharedAAffineNielsPointCompletedPoint
