/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Math.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Affine Montgomery Curve Points for Curve25519

This file defines affine point arithmetic on Montgomery curves,
focusing on the affine coordinate representation (u, v).

## Contents

1. **Field Definitions**: `CurveField` as `ZMod p` where p = 2^255 - 19
2. **Affine Point Structure**: Points (u, v) satisfying v² = u³ + A·u² + u
3. **Group Law**: Addition formulas and group structure for affine points
from Mathlib EllipticCurve.Affine.Point

## References

* Costello, Craig and Smith, Benjamin: "Montgomery curves and their arithmetic" (2017)
  https://eprint.iacr.org/2017/212.pdf
* Bernstein, Daniel J.: "Curve25519: new Diffie-Hellman speed records" (2006)
  https://cr.yp.to/ecdh/curve25519-20060209.pdf
-/

namespace Montgomery

open ZMod
open WeierstrassCurve.Affine.Point

/-! ## Mathematical Foundations -/

/-- The finite field F_p where p = 2^255 - 19. -/
abbrev CurveField : Type := ZMod p

instance : Fact (Nat.Prime p) := ⟨PrimeCert.prime_25519''⟩

instance : NeZero (2 : CurveField) := ⟨by decide⟩

-- Enable decidable equality for the field (required for mathlib's AddCommGroup instance)
open scoped Classical in
noncomputable instance : DecidableEq CurveField := inferInstance



theorem lift_mod_eq_iff (a b : ℕ) : (a ≡ b  [MOD p]) ↔  (a : CurveField) = (b : CurveField) := by
  sorry
theorem lift_mod_add (a b : ℕ) : (a : CurveField) + (b : CurveField) = ((a +b):CurveField) := by
  sorry
theorem lift_mod_mul (a b : ℕ) : (a : CurveField) * (b : CurveField) = ((a * b):CurveField) := by
  sorry
theorem mod_nat_mul_mod (a b : ℕ) : (a) * (b % p) ≡ a * b [MOD p] := by
  sorry
/-- A Montgomery curve structure defined by parameters A and B.
    The curve equation is: B·v² = u³ + A·u² + u -/
def Curve25519.A := (486662 : CurveField)

def MontgomeryCurveCurve25519 : WeierstrassCurve.Affine CurveField :=
  { a₁ := 0
    a₂ := Curve25519.A
    a₃ := 0
    a₄ := 1
    a₆ := 0 }

abbrev Point :=  MontgomeryCurveCurve25519.Point

lemma zero_def : (0 : Point) = .zero := sorry
def T_point : Point := .some (x := 0) (y := 0) (h := by
  constructor
  · norm_num [MontgomeryCurveCurve25519]
  · left
    norm_num [MontgomeryCurveCurve25519, Curve25519.A])

theorem T_point_order_two : T_point + T_point = 0 := by
  sorry
theorem non_singular {u v : CurveField}
    (h : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
    v ≠ 0 ∨ 3 * u ^ 2 + 2 * Curve25519.A * u + 1 ≠ 0  := by
  sorry
lemma nonsingular_iff (x y : CurveField) : MontgomeryCurveCurve25519.Nonsingular x y ↔ MontgomeryCurveCurve25519.Equation x y := by
  sorry
/-- Create a point from coordinates with curve equation proof and nonsingular condition. -/
def mk_point {u v : CurveField}
    (h : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u := by grind) :
    Point :=
  .some ((nonsingular_iff u v).mpr (by
        rw[WeierstrassCurve.Affine.equation_iff]
        simp only [MontgomeryCurveCurve25519]
        simp[h]))

theorem ext (u v x y : CurveField) (equx : u = x) (eqvy : v = y)
  (huv : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u)
  (hxy : y ^ 2 = x ^ 3 + Curve25519.A * x ^ 2 + x) :
  mk_point huv = mk_point hxy := by
  sorry
/-- Extract u-coordinate from a point. -/
def get_u : Point → CurveField
  | .zero => 0
  | .some (x := u) .. => u

def get_v : Point → CurveField
  | .zero => 0
  | .some (y := v) .. => v

@[simp] theorem get_u_zero : get_u (0: Point) = 0 := rfl
@[simp] theorem get_v_zero : get_v (0: Point) = 0 := rfl

@[simp] theorem get_u_T : get_u T_point = 0 := rfl
@[simp] theorem get_v_T : get_v T_point = 0 := rfl

@[simp] theorem neg_u_coord (P : Point) :
    get_u (-P) = get_u P := by cases P <;> rfl

@[simp] theorem neg_v_coord (P : Point) :
    get_v (-P) = -(get_v P) := by
  cases P
  · rfl
  · simp [get_v, MontgomeryCurveCurve25519]

/-- The coordinates of a non-zero point satisfy the curve equation. -/
theorem point_on_curve (P : Point) (hP : P ≠ 0) :
    get_v P ^ 2 = get_u P ^ 3 + Curve25519.A * get_u P ^ 2 + get_u P := by
  sorry
theorem mk_point_def (P : Point) (hP : P ≠ 0) :
    P = mk_point (point_on_curve P hP) := by
  sorry
theorem get_u_v_inj (P Q : Point) (nonP : P ≠ 0) (nonQ : Q ≠ 0) (hu : get_u P = get_u Q) (hv : get_v P = get_v Q) :
  P=Q := by
  sorry
theorem get_u_v_inj_neg (P Q : Point) (nonP : P ≠ 0) (nonQ : Q ≠ 0) (hu : get_u P = get_u Q) (hv : get_v P = -get_v Q) :
  P=-Q := by
  sorry
theorem mk_point_T {P : Point} (hP : P ≠ 0) (hu : get_u P = 0) (hv : get_v P = 0) :
  P=T_point:= by
  sorry
theorem mk_point_neq_zero {u v : CurveField} (h : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
 mk_point h ≠ 0 := by
  sorry
@[simp] theorem get_u_mk_point {u v : CurveField}
    (h : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
    get_u (mk_point h) = u := rfl

@[simp] theorem get_v_mk_point {u v : CurveField}
    (h : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
    get_v (mk_point h) = v := rfl

@[simp] theorem mk_point_neq_T_of_u {u v : CurveField}
    (hu : u ≠ 0)
    (h : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
    (mk_point h) ≠ T_point  := by
    unfold mk_point T_point
    simp[hu]

@[simp] theorem mk_point_neq {u₁ v₁ u₂ v₂ : CurveField}
    (hu : u₁ ≠ u₂)
    (h₁ : v₁ ^ 2 = u₁ ^ 3 + Curve25519.A * u₁ ^ 2 + u₁)
    (h₂ : v₂ ^ 2 = u₂ ^ 3 + Curve25519.A * u₂ ^ 2 + u₂) :
    (mk_point h₁) ≠ (mk_point h₂)  := by
    unfold mk_point
    simp[hu]


@[simp] theorem mk_point_neq_neg {u₁ v₁ u₂ v₂ : CurveField}
    (hu : u₁ ≠ u₂)
    (h₁ : v₁ ^ 2 = u₁ ^ 3 + Curve25519.A * u₁ ^ 2 + u₁)
    (h₂ : v₂ ^ 2 = u₂ ^ 3 + Curve25519.A * u₂ ^ 2 + u₂) :
    (mk_point h₁) ≠ (-mk_point h₂)  := by
    unfold mk_point
    simp[hu]





/-! ### Group Law Properties -/

/-- Addition is commutative for points.
This follows directly from mathlib's AddCommGroup instance for Weierstrass curve points. -/
theorem add_comm (P Q : Point) : P + Q = Q + P := sorry
theorem uADD (P Q : Point)
  (PZero : P ≠ 0) (QZero : Q ≠ 0)
  (nPT : P ≠ T_point) (nQT : Q ≠ T_point)
  (PQ : P ≠ Q) (PQ : P ≠ -Q) :
  get_u (P + Q) * get_u (P - Q) * (get_u P - get_u Q)^2  = (get_u P * get_u Q - 1)^2 := by
  sorry
lemma non_IsQuase : ¬ IsSquare ((Curve25519.A^2 -4)) := by
  sorry
lemma A_mius_two_non_square : ¬ IsSquare (Curve25519.A - 2) := by
  sorry
lemma A_plus_two_square :  IsSquare (Curve25519.A + 2) := by
  sorry
lemma quadratic_ne_zero (x : CurveField) : ¬ x ^ 2 + Curve25519.A * x + 1 = 0 := by
  sorry
theorem DBL_neq_zero (P : Point) (PZero : P ≠ 0) (nPT : P ≠ T_point) :
  2 • P ≠ 0 := by
  sorry
theorem uDBL (P : Point) (PZero : P ≠ 0) (nPT : P ≠ T_point) :
  4 * get_u (2 • P) * get_u (P) * ((get_u P)^2 +  Curve25519.A * get_u P + 1) = ((get_u P) ^ 2 - 1)^2 := by
  sorry
/-- Addition is associative for points.
This follows directly from mathlib's AddCommGroup instance for Weierstrass curve points. -/
theorem add_assoc' (P Q R : Point) : (P + Q) + R = P + (Q + R) := sorry
theorem add_mk_point (m₁ m₂ : Point)
    (hsum : (m₁ + m₂) ≠ 0) :
    m₁ + m₂ = mk_point  (point_on_curve (m₁ + m₂) hsum) := by
  sorry
@[simp]
lemma slope_of_Y_eq {x₁ x₂ y₁ y₂ : CurveField} (hx : x₁ = x₂) (hy : y₁ = -y₂) :
    MontgomeryCurveCurve25519.slope x₁ x₂ y₁ y₂ = 0 := by
  sorry
@[simp]
lemma slope_of_Y_ne' {x₂ y₁ y₂ : CurveField} (hy : ¬y₁ = -y₂) :
    MontgomeryCurveCurve25519.slope x₂ x₂ y₁ y₂ =
      (3 * x₂ ^ 2 + 2 * Curve25519.A * x₂ + 1) / (2* y₁)  := by
  sorry
@[simp]
lemma slope_of_Y_ne {x₁ x₂ y₁ y₂ : CurveField} (hx : x₁ = x₂) (hy : y₁ ≠ -y₂) :
    MontgomeryCurveCurve25519.slope x₁ x₂ y₁ y₂ =
      (3 * x₁ ^ 2 + 2 * Curve25519.A  * x₁ + 1) / (2*y₁ ) := by
  sorry
@[simp]
lemma slope_of_X_ne {x₁ x₂ y₁ y₂ : CurveField} (hx : x₁ ≠ x₂) :
    MontgomeryCurveCurve25519.slope x₁ x₂ y₁ y₂ = (y₁ - y₂) / (x₁ - x₂) := by
  sorry
lemma addX_eq_addX_negY_sub {x₁ x₂ : CurveField} (y₁ y₂ : CurveField) (hx : x₁ ≠ x₂) :
    MontgomeryCurveCurve25519.addX x₁ x₂ (MontgomeryCurveCurve25519.slope x₁ x₂ y₁ y₂) = MontgomeryCurveCurve25519.addX x₁ x₂ (MontgomeryCurveCurve25519.slope x₁ x₂ y₁ <| MontgomeryCurveCurve25519.negY x₂ y₂) -
      (y₁ - MontgomeryCurveCurve25519.negY x₁ y₁) * (y₂ - MontgomeryCurveCurve25519.negY x₂ y₂) / (x₂ - x₁) ^ 2 := by
  sorry
lemma addX_spec {x₁ x₂ : CurveField} (y₁ y₂ : CurveField) (hx : x₁ ≠ x₂) :
  MontgomeryCurveCurve25519.addX x₁ x₂ (MontgomeryCurveCurve25519.slope x₁ x₂ y₁ y₂)
  = ((y₁ - y₂) / (x₁ - x₂) )^2 - Curve25519.A - x₁ - x₂ := by
  sorry
end Montgomery
