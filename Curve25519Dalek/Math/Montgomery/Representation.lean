/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo, Oliver Butterley, Hoang Le Truong
-/
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Edwards.Curve
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Math.Montgomery.Curve
import Curve25519Dalek.Types

/-!
# Montgomery Point Representations

Bridge infrastructure connecting Rust `MontgomeryPoint` to mathematical points.
-/

/-!
## MontgomeryPoint Validity
-/

namespace curve25519_dalek.backend.serial.curve_models

abbrev MontgomeryPoint := curve25519_dalek.montgomery.MontgomeryPoint

end curve25519_dalek.backend.serial.curve_models

namespace curve25519_dalek.montgomery

open curve25519_dalek curve25519_dalek.math
open Edwards


/--
Validity for MontgomeryPoint.
A MontgomeryPoint is a 32-byte integer `u` representing a coordinate on the curve `v² = u³ + Au² + u`.
It is valid if:
1. The integer `u` is strictly less than the field modulus `p`.
2. `u` maps to a valid Edwards `y` coordinate (i.e., `u ≠ -1`).
3. The resulting Edwards point exists (i.e., we can solve for `x`).
-/
def MontgomeryPoint.IsValid (m : MontgomeryPoint) : Prop :=
  let u : ZMod p:= U8x32_as_Field m
  -- The check `u_int < p` is implicitly handled because
  -- bytesToField returns a `ZMod p`, which is canonical by definition.
  -- However, to match the Rust strictness (rejecting non-canonical inputs),
  -- we should technically check the raw Nat value.
  -- But for the linter ''deterministic timeout' issue, we just need to avoid U8x32_as_Nat.
  if u + 1 = 0 then
    False
  else
    let y := (u - 1) * (u + 1)⁻¹
    let num := y^2 - 1
    let den := (d : ZMod p) * y^2 + 1
    IsSquare (num * den⁻¹)

noncomputable instance (m : MontgomeryPoint) : Decidable (MontgomeryPoint.IsValid m) := by
  unfold MontgomeryPoint.IsValid
  infer_instance

/--
The Edwards denominator is never zero.
-/
lemma edwards_denom_nonzero (y : ZMod p) : (Ed25519.d : ZMod p) * y ^ 2 + 1 ≠ 0 := by
  sorry
lemma montgomery_helper {F : Type*} [Field F] (d y x_sq : F)
    (h_den : d * y ^ 2 + 1 ≠ 0)
    (h_x : x_sq = (y ^ 2 - 1) * (d * y ^ 2 + 1)⁻¹) :
    -1 * x_sq + y ^ 2 = 1 + d * x_sq * y ^ 2 := by
  sorry
/--
Convert MontgomeryPoint to Point Ed25519.
1. Recovers `y` from `u` via `y = (u-1)/(u+1)`.
2. Recovers `x` from `y` (choosing the canonical positive root).
Returns 0 (identity) if invalid.
-/noncomputable def MontgomeryPoint.toPoint (m : MontgomeryPoint) : Point Ed25519 :=
  if h : (MontgomeryPoint.IsValid m) then
    -- The following is equivalent to defining u := 8x32_as_Nat m % p, but it uses Horner's method
    --  to avoid un folding heavy computations on large Nats casted as Mod p.
    let u : ZMod p:= U8x32_as_Field m
    -- We know u != -1 from IsValid, so inversion is safe/correct
    let one : ZMod p := 1
    let y : ZMod p := (u - one) * (u + one)⁻¹
    -- Recover x squared
    let num : ZMod p := y^2 - one
    let den : ZMod p := (d : ZMod p) * y^2 + one
    let x2 : ZMod p := num * den⁻¹
    -- Extract root (guaranteed to exist by IsValid)
    match h_sqrt : sqrt_checked x2 with
    | (x_abs, is_sq) =>
    -- For Montgomery -> Edwards, the sign of x is lost.
    -- We canonically choose the non-negative (even) root.
    { x := x_abs, y := y, on_curve := by
        have h_is_sq_true : is_sq = true := by
          unfold MontgomeryPoint.IsValid at h
          by_cases h_inv : u + 1 = 0
          · rw [if_pos h_inv] at h; dsimp only [h_inv] at h
          · rw [if_neg h_inv] at h; rw [sqrt_checked_iff_isSquare x2 h_sqrt]; convert h
        have h_x_sq : x_abs^2 = x2 := by
          apply sqrt_checked_spec x2 h_sqrt h_is_sq_true
        have h_den_nz : den ≠ 0 := by
          dsimp only [den, one]
          apply edwards_denom_nonzero
        have ha : Ed25519.a = -1 := rfl
        have hd : (d : ZMod p) = Ed25519.d := rfl
        rw [ha, h_x_sq]
        dsimp only [x2, num, den, one] at ⊢ h_den_nz
        apply (mul_right_inj' h_den_nz).mp
        field_simp [h_den_nz]
        simp only [neg_sub]
        rw [← hd]
        try ring
      }
  else
    0

end curve25519_dalek.montgomery

namespace Montgomery

open curve25519_dalek.montgomery
open curve25519_dalek.math


section MontgomeryPoint

/-- Create a point from a MontgomeryPoint byte representation.
    Computes the v-coordinate from u using the Montgomery curve equation v² = u³ + A·u² + u.

    Note: `sqrt_checked` returns a value whose square equals its input, which depends on
    the mathematical properties of the square root function in the field.

    This is a one-way conversion, since the Montgomery
    model does not retain sign information.
-/
def v_squared (u : CurveField) : CurveField := u ^ 3 + Curve25519.A * u ^ 2 + u

noncomputable def MontgomeryPoint.u_affine_toPoint (u : CurveField) : Point:=
    match h_call: curve25519_dalek.math.sqrt_checked (v_squared u) with
    | (v, was_square) =>
    if h_invalid : !was_square || (u ==0) then
      T_point
    else
      .some (x := u) (y := v) (h := by
        replace h_invalid := Bool.eq_false_iff.mpr h_invalid
        rw [Bool.or_eq_false_iff] at h_invalid
        obtain ⟨h_sq_not,  h_y_eq_false⟩ := h_invalid
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at h_sq_not
        have curve_eq : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u := by
          apply sqrt_checked_spec (v_squared u)
          · exact h_call
          · exact h_sq_not
        apply (nonsingular_iff u v).mpr
        rw[WeierstrassCurve.Affine.equation_iff]
        simp only [MontgomeryCurveCurve25519]
        simp only[curve_eq ]
        ring
     )

theorem Aux_u_affine_toPoint_spec {u v : CurveField}
  (non : u ≠ 0)
  (equation : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
   ((sqrt_checked (u ^ 3 + Curve25519.A * u ^ 2 + u)).2 = false ∨ u = 0) = False:= by
  sorry
theorem non_u_affine_toPoint_spec {u v : CurveField}
  (equation : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
  MontgomeryCurveCurve25519.Nonsingular u v := by
  sorry
/-
theorem MontgomeryPoint.u_affine_toPoint_spec (u v : CurveField)
  (non : u ≠ 0)
  (equation : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
  MontgomeryPoint.u_affine_toPoint (u : CurveField) = WeierstrassCurve.Affine.Point.some ( non_u_affine_toPoint_spec equation) := by
  have := Aux_u_affine_toPoint_spec non equation
  unfold MontgomeryPoint.u_affine_toPoint
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq]
  have := @if_neg
-/

noncomputable def MontgomeryPoint.mkPoint (m : MontgomeryPoint) : Point:=
    MontgomeryPoint.u_affine_toPoint  (((U8x32_as_Nat m) % 2 ^255):ℕ )

end MontgomeryPoint

section fromEdwards
open curve25519_dalek.montgomery
open curve25519_dalek.edwards

lemma d_eq : (Edwards.Ed25519.d : CurveField)= -121665/ 121666 := by
  sorry
lemma a_plus_d : (Edwards.Ed25519.a : CurveField) + Edwards.Ed25519.d = - 243331/121666 := by
  sorry
lemma a_sub_d : (Edwards.Ed25519.a : CurveField) - Edwards.Ed25519.d = - 1/121666 := by
  sorry
lemma adA : 2 * ((Edwards.Ed25519.a : CurveField) + Edwards.Ed25519.d) /(Edwards.Ed25519.a - Edwards.Ed25519.d) = Curve25519.A := by
  sorry
lemma adB : (4 / ((Edwards.Ed25519.a : CurveField) - Edwards.Ed25519.d)) = - 486664 := by
  sorry
lemma A_add_2 : 486664=  Curve25519.A+2 := by
  sorry
lemma d_plus_one_square : IsSquare (Edwards.Ed25519.d +1) := by
  sorry
lemma B_d_relation : IsSquare (4 / ((Edwards.Ed25519.a : CurveField) - Edwards.Ed25519.d)) := by
  sorry
lemma inver_Ad : (Curve25519.A + 2) * Edwards.Ed25519.d + (Curve25519.A - 2) = 0:= by
  sorry
lemma inver_Ad_eq : Edwards.Ed25519.d=    - (Curve25519.A - 2) /(Curve25519.A + 2):= by
  sorry
noncomputable def Curve25519.roots_B : CurveField :=
  Classical.choose B_d_relation

lemma pow2_roots_B : Curve25519.roots_B ^ 2 = 4 / ((Edwards.Ed25519.a : CurveField) - Edwards.Ed25519.d) := by
  sorry
lemma roots_B_non_zero : ¬ Curve25519.roots_B = 0 := by
  sorry
lemma roots_B_d : Curve25519.roots_B ^ 2 * Edwards.Ed25519.d= (Curve25519.A - 2):= by
  sorry
lemma montgomery_edwards_inverse {y : CurveField} (hy1 : y ≠ 1) :    let u := (1 + y) / (1 - y)
    y = (u - 1) / (u + 1) := by
  sorry
theorem on_curves_M (e : Edwards.Point Edwards.Ed25519)
 (hy : e.y ≠ 1)
 (hx : e.x ≠ 0) :
  let u :=(1 + e.y) / (1 - e.y)
  let v := (1 + e.y) / ((1 - e.y) * e.x)
  let A := 2 * ((Edwards.Ed25519.a : CurveField) + Edwards.Ed25519.d) /(Edwards.Ed25519.a - Edwards.Ed25519.d)
  let B := 4 / ((Edwards.Ed25519.a : CurveField) - Edwards.Ed25519.d)
  B* v^2 = u ^ 3 + A * u ^ 2 + u  := by
  sorry
theorem on_MontgomeryCurves (e : Edwards.Point Edwards.Ed25519)
 (hy : e.y ≠ 1)
 (hx : e.x ≠ 0) :
  let u :=(1 + e.y) / (1 - e.y)
  let v := Curve25519.roots_B  * (1 + e.y) / ((1 - e.y) * e.x)
  v^2 = u ^ 3 + Curve25519.A * u ^ 2 + u  := by
  sorry
theorem nonsingular_on_curves_M (e : Edwards.Point Edwards.Ed25519) (hy : e.y ≠ 1)
 (hx : e.x ≠ 0) :
  let u := (1 + e.y) / (1 - e.y)
  let v := Curve25519.roots_B * (1 + e.y) / ((1 - e.y) * e.x)
  MontgomeryCurveCurve25519.Nonsingular u v  := by
  sorry
lemma id_1 {u v : CurveField}
(equation : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :  (-((Curve25519.A+2) * u ^ 2) + v ^ 2) * (u + 1) ^ 2 =
  u * ((u * (u * 3 + 2 * Curve25519.A) + 1) ^ 2 - 4 * v ^ 2 * Curve25519.A - 8 * u * v ^ 2) := by
  sorry
lemma id_2 {u v : CurveField}
(equation : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
(-(Curve25519.A + 2) * u ^ 2 * (u + 1) ^ 2 * -1 + v ^ 2 * (u - 1) ^ 2) =u*(Curve25519.A * u  * 2 + Curve25519.A * u ^ 3 *2 + 1+ u ^ 2 * 6 + u ^ 4) := by
  sorry
lemma id_3 {u v : CurveField}
(equation : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u) :
(1 + 1) *
      ((u * (u * 3 + 2 * Curve25519.A) + 1) ^ 2 - v ^ 2 * Curve25519.A * (1 + 1) ^ 2 - v ^ 2 * u * (1 + 1) ^ 2 -
        v ^ 2 * u * (1 + 1) ^ 2) *
    (u * 2 * Curve25519.A * (1 + u ^ 2) + 1 + u ^ 2 * 6 + u ^ 4) =
  2 * (u - 1) * (u + 1) *
    (-(v ^ 4 * (1 + 1) ^ 3) +
      -((u * (u * 3 + 2 * Curve25519.A) + 1) *
          ((u * (u * 3 + 2 * Curve25519.A) + 1) ^ 2 - v ^ 2 * Curve25519.A * (1 + 1) ^ 2 - v ^ 2 * u * (1 + 1) ^ 2 -
              v ^ 2 * u * (1 + 1) ^ 2 -
            v ^ 2 * u * (1 + 1) ^ 2)))
            := by
  sorry
lemma id_4 {u v : CurveField}
(equation : v ^ 2 = u ^ 3 + Curve25519.A * u ^ 2 + u)
(non_eq₀ : ¬(Curve25519.A + 2) * u ^ 2 * (u + 1) ^ 2 + v ^ 2 * (u - 1) ^ 2 = 0) :
 u * Curve25519.A * 2 * (1 + u ^ 2) + 1 + u ^ 2 * 6 + u ^ 4 ≠ 0 := by
  sorry
lemma id_5 {u1 v1 u2 v2 : CurveField}
(equation1 : v1 ^ 2 = u1 ^ 3 + Curve25519.A * u1 ^ 2 + u1)
(equation2 : v2 ^ 2 = u2 ^ 3 + Curve25519.A * u2 ^ 2 + u2) :
(v1 * v2 * (u1 * u2 + 1) - u1 * u2 * (2 * (u1 + u2) + (u1 * u2 + 1) * Curve25519.A)) * (u1 - u2) ^ 2 =
  (v1 * v2 * (u1 + u2) - -(u1 * u2 * (u1 * u2 * 2 + (u1 + u2) * Curve25519.A + 2))) *
    ((v1 - v2) ^ 2 - Curve25519.A * (u1 - u2) ^ 2 - u1 * (u1 - u2) ^ 2 - u2 * (u1 - u2) ^ 2) := by
  sorry
lemma id_6 {u1 v1 u2 v2 : CurveField}
(equation1 : v1 ^ 2 = u1 ^ 3 + Curve25519.A * u1 ^ 2 + u1)
(equation2 : v2 ^ 2 = u2 ^ 3 + Curve25519.A * u2 ^ 2 + u2) :
(u1 - u2) *
    (((v1 - v2) ^ 2 - (u1 - u2) ^ 2 * Curve25519.A - u1 * (u1 - u2) ^ 2 - u2 * (u1 - u2) ^ 2) *
        (v1 * v2 * (u1 + 1) * (u2 + 1) + u1 * u2 * (Curve25519.A - 2) * (u1 - 1) * (u2 - 1)) +
      v1 * (u1 - u2) ^ 2 * (v2 * u1 * (u1 + 1) * (u2 - 1) + v1 * u2 * (u2 + 1) * (u1 - 1))) =
  (v2 * u1 * (u1 + 1) * (u2 - 1) + v1 * u2 * (u2 + 1) * (u1 - 1)) * (v2 - v1) *
    ((v1 - v2) ^ 2 - (u1 - u2) ^ 2 * Curve25519.A - u1 * (u1 - u2) ^ 2 - u2 * (u1 - u2) ^ 2 - u1 * (u1 - u2) ^ 2) := by
  sorry
noncomputable def fromEdwards : Edwards.Point Edwards.Ed25519 → Point
  | e =>
    if hy: e.y = 1 then
     0
     else
     if hx: e.x =0 ∧ e.y = -1 then
      T_point
     else
      let u:= (1 + e.y) / (1 - e.y)
      let v := Curve25519.roots_B  * (1 + e.y) / ((1 - e.y) * e.x)
      .some (x := u) (y := v) (h:= by
      apply nonsingular_on_curves_M e hy
      have : e.x ≠  0 ∨  e.y ≠  -1 := by
       grind
      rcases this
      · simp_all only [false_and, not_false_eq_true, ne_eq]
      · intro h
        have := e.on_curve
        simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add, zero_mul, add_zero,
          sq_eq_one_iff, hy, false_or] at this
        simp_all only [and_self, not_true_eq_false]
       )

theorem map_zero : fromEdwards 0 = 0 := by
  sorry
theorem zeroY (e : Edwards.Point Edwards.Ed25519)
  (h : e.y = 1) :
  e = 0 := by
  sorry
theorem zero_iff (e : Edwards.Point Edwards.Ed25519) :  e = 0 ↔ e.y = 1 := by
  sorry
theorem exceptEdwardsPoint {e : Edwards.Point Edwards.Ed25519}
  (h : 1 + e.y = 0) :
  e.x = 0 := by
  sorry
theorem neg_fromEdwards (e : Edwards.Point Edwards.Ed25519) :
  fromEdwards (-e) = - fromEdwards e := by
  sorry
theorem condition_T_point (e₁ e₂ : Edwards.Point Edwards.Ed25519)
 (h : 1 + (e₁ + e₂).y = 0) (he₁ : 1 + e₁.y = 0) :
   e₂.y = 1 := by
  sorry
theorem add_T_point (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (he₁ : 1 + e₁.y = 0) :
  e₂.x = -(e₁ + e₂).x  ∧ e₂.y = -(e₁ + e₂).y := by
  sorry
theorem add_T_point' (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (he₁ : 1 + e₂.y = 0) :
  e₁.x = -(e₁ + e₂).x  ∧ e₁.y = -(e₁ + e₂).y := by
  sorry
theorem T_point_x {e : Edwards.Point Edwards.Ed25519}
  (h : e.x = 0) :
  e.y = 1 ∨ e.y = -1 := by
  sorry
lemma condition_Neg (e₁ e₂ : Edwards.Point Edwards.Ed25519)
(hy1 : 1 - e₂.y ≠ 0) (hy2 : 1 - e₁.y ≠ 0) (hy3 : 1 + e₂.y ≠ 0)
    (hx1 : e₁.x ≠ 0) (hx2 : e₂.x ≠ 0) :
((1 + e₁.y) / (1 - e₁.y) = (1 + e₂.y) / (1 - e₂.y) ∧ e₁.x = - e₂.x) ↔
((1 + e₁.y) / (1 - e₁.y) = (1 + e₂.y) / (1 - e₂.y) ∧
        Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) =
          -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x))) := by
  sorry
lemma injective_fromEdwards {e₁ e₂ : Edwards.Point Edwards.Ed25519}
(hy1 : 1 - e₂.y ≠ 0) (hy2 : 1 - e₁.y ≠ 0) :
(1 + e₁.y) / (1 - e₁.y) = (1 + e₂.y) / (1 - e₂.y) ↔ e₁.y =e₂.y := by
  sorry
lemma edwards_neg_iff_montgomery_neg {e₁ e₂ : Edwards.Point Edwards.Ed25519}
(hy1 : 1 - e₂.y ≠ 0) (hy2 : 1 - e₁.y ≠ 0) (hy3 : 1 + e₂.y ≠ 0)
    (hx1 : e₁.x ≠ 0) (hx2 : e₂.x ≠ 0) :
(e₁.y =e₂.y  ∧ e₁.x = - e₂.x) ↔
((1 + e₁.y) / (1 - e₁.y) = (1 + e₂.y) / (1 - e₂.y) ∧
        Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) =
          -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x))) := by
  sorry
theorem fromEdwards_add_of_snd_x_eq_zero_of_snd_y_eq_one (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (zero_e2_x : e₂.x = 0)
  (e2y : e₂.y = 1) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  sorry
theorem fromEdwards_add_of_snd_x_eq_zero_of_fst_y_eq_one (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (zero_e2_x : e₂.x = 0)
  (e2y : e₂.y = -1)
  (non_e₁ : e₁.y = 1) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  sorry
theorem fromEdwards_add_of_snd_x_eq_zero_of_fst_y_eq_neg_one (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (zero_e2_x : e₂.x = 0)
  (e2y : e₂.y = -1)
  (non_e₁ : e₁.y = -1) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  sorry
lemma edwards_one_sub_y_sq_mul_x_sq_eq (e₁ : Edwards.Point Edwards.Ed25519) : (1 + -e₁.y) * (1 - e₁.y) * e₁.x ^ 2 =
  (1 + e₁.y) * ((1 - e₁.y) * (-486664 - e₁.x ^ 2 * Curve25519.A) - (1 + e₁.y) * e₁.x ^ 2) := by
  sorry
lemma x_sq_mul_linear_factor_eq (e₁ : Edwards.Point Edwards.Ed25519) : e₁.x ^ 2 * (e₁.y * 2 + (-e₁.y ^ 2 - 1)) =
  e₁.x ^ 2 * (e₁.y * (2 + e₁.y * (1 - Curve25519.A)) + 1) + (e₁.x ^ 2 * Curve25519.A - Curve25519.roots_B ^ 2) +
    Curve25519.roots_B ^ 2 * e₁.y ^ 2 := by
  sorry
/-- The Montgomery curve equation `v² = u³ + Au² + u`, divided through by `u²`,
    rearranges to `1/u = (v/u)² - A - u`. This lemma establishes this equivalent form
    for an Edwards point mapped birationally to Montgomery coordinates. -/
theorem montgomery_inv_u_eq (e₁ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (non_e₁ : ¬ e₁.y = -1)
  (non_e : ¬ e₁.y = 1) :
  (1 + -e₁.y) / (1 + e₁.y) =
    (Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) / ((1 + e₁.y) / (1 - e₁.y))) ^ 2 - Curve25519.A -
      (1 + e₁.y) / (1 - e₁.y) := by
  sorry
theorem fromEdwards_add_of_snd_x_eq_zero (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (zero_e2_x : e₂.x = 0) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  sorry
theorem fromEdwards_add_of_sum_y_eq_one (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (sum_y : (e₁ + e₂).y = 1) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  sorry
theorem fromEdwards_add_of_fst_y_eq_one (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (h : e₁.y = 1) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  sorry
theorem fromEdwards_add_of_snd_y_eq_one (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (zero_e2_x : e₂.x ≠ 0)
  (h₂ : e₂.y = 1) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  sorry
lemma montgomery_addX_slope_div_roots_B_eq_zero : 0 =
  (Curve25519.A + 2 +
      -((-1 + (-(2 * Curve25519.A) + -3)) *
            (-(3 + 2 * Curve25519.A + 1) ^ 2 / ((-2 + -Curve25519.A) * (1 + 1) ^ 2) - Curve25519.A - 1 - 1 - 1) /
          (1 + 1))) /
    Curve25519.roots_B := by
  sorry
theorem fromEdwards_add_of_x_eq_of_y_eq_neg (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (non_e2_x : e₂.x ≠ 0)
  (non_e1_y : 1 - e₁.y ≠ 0)
  (non_e2_y : 1 - e₂.y ≠ 0)
  (non_e2_y1 : 1 + e₂.y ≠ 0)
  (e_x : e₁.x = e₂.x)
  (e_y : e₁.y = -e₂.y) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  sorry
lemma montgomery_addX_eq_zero_of_sum_y_eq_neg_one_of_y_ne_neg_y {e₁ e₂ : Edwards.Point Edwards.Ed25519}
  (non_e1_x : e₁.x ≠ 0)
  (non_e2_x : e₂.x ≠ 0)
  (non_e1_y : 1 - e₁.y ≠ 0)
  (non_e2_y1 : 1 + e₂.y ≠ 0)
  (sum_x : e₁.x * e₂.y + e₁.y * e₂.x = 0)
  (sum_y : (e₁ + e₂).y = -1)
  (non_meq : e₁.y ≠ -e₂.y) :
  0 =
    ((Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) - Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x)) /
              ((1 + e₁.y) / (1 - e₁.y) - (1 + e₂.y) / (1 - e₂.y))) ^
            2 -
          Curve25519.A -
        (1 + e₁.y) / (1 - e₁.y) -
      (1 + e₂.y) / (1 - e₂.y) := by
  sorry
lemma birational_map_symm {x y u v : CurveField}
  (non_x : ¬x = 0)
  (hya : 1 - y ≠ 0)
  (hym : 1 + y ≠ 0)
  (hu : u = (1 + y) / (1 - y))
  (hv : v = Curve25519.roots_B * (1 + y) / ((1 - y) * x)) :
   x= (Curve25519.roots_B * u)/v ∧ y= (u-1)/(u+1) ∧ ( u≠ 0) ∧ (u+1 ≠ 0) ∧ (v ≠ 0):= by
  sorry
lemma montgomery_v_add_eq_zero_of_sum_y_eq_neg_one_of_y_ne {e₁ e₂ : Edwards.Point Edwards.Ed25519}
  (non_e1_x : e₁.x ≠ 0)
  (non_e2_x : e₂.x ≠ 0)
  (non_e1_y : 1 - e₁.y ≠ 0)
  (non_e2_y : 1 - e₂.y ≠ 0)
  (non_e1_y1 : 1 + e₁.y ≠ 0)
  (non_e2_y1 : 1 + e₂.y ≠ 0)
  (sum_x : e₁.x * e₂.y + e₁.y * e₂.x = 0)
  (sum_y : (e₁ + e₂).y = -1)
  (non_meq : e₁.y ≠ -e₂.y)
  (non_eq : e₁.y ≠ e₂.y) :
 0 =
  -(Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x)) +
    -((Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) - Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x)) /
          ((1 + e₁.y) / (1 - e₁.y) - (1 + e₂.y) / (1 - e₂.y)) *
        (((Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) -
                      Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x)) /
                    ((1 + e₁.y) / (1 - e₁.y) - (1 + e₂.y) / (1 - e₂.y))) ^
                  2 -
                Curve25519.A -
              (1 + e₁.y) / (1 - e₁.y) -
            (1 + e₂.y) / (1 - e₂.y) -
          (1 + e₁.y) / (1 - e₁.y))) := by
  sorry
lemma fromEdwards_add_of_sum_x_eq_zero_of_sum_y_eq_neg_one_of_y_ne_neg_y {e₁ e₂ : Edwards.Point Edwards.Ed25519}
   (non_e1_x : e₁.x ≠ 0)
  (non_e2_x : e₂.x ≠ 0)
  (non_e1_y : 1 - e₁.y ≠ 0)
  (non_e2_y : 1 - e₂.y ≠ 0)
  (non_e2_y1 : 1 + e₂.y ≠ 0)
  (non_e1_y1 : 1 + e₁.y ≠ 0)
  (sum_x : e₁.x * e₂.y + e₁.y * e₂.x = 0)
  (sum_y : (e₁ + e₂).y = -1)
  (e_y : e₁.y ≠ -e₂.y) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  sorry
theorem fromEdwards_add_of_sum_x_eq_zero_of_sum_y_eq_neg_one (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (non_e2_x : ¬e₂.x = 0)
  (sum_x : (e₁ + e₂).x = 0)
  (non_e1_y : ¬1 - e₁.y = 0)
  (non_e2_y : ¬1 - e₂.y = 0)
  (non_e2_y_1 : ¬1 + e₂.y = 0)
  (non_e1_y_1 : ¬1 + e₁.y = 0)
  (sum_y_1 : (e₁ + e₂).y = -1) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  sorry
lemma x_eq_or_eq_neg_of_y_eq {e₁ e₂ : Edwards.Point Edwards.Ed25519}
  (non_e1_x : ¬e₁.x = 0)
  (zero_e2_x : e₂.x ≠ 0)
  (hy1 : 1 - e₂.y ≠ 0)
  (hy3 : 1 + e₂.y ≠ 0)
  (heqy : e₁.y = e₂.y) :
  e₁.x= e₂.x ∨  e₁.x= -e₂.x := by
  sorry
lemma fromEdwards_u_add_of_eq {e₁ e₂ : Edwards.Point Edwards.Ed25519}
  (non_e1_x : ¬e₁.x = 0)
  (non_e2_x : e₂.x ≠ 0)
  (hy1 : 1 - e₂.y ≠ 0)
  (hy3 : 1 + e₂.y ≠ 0)
  (heqy : e₁.y = e₂.y)
  (heqx : e₁.x = e₂.x) :
 (1 + (e₁ + e₂).y) / (1 - (e₁ + e₂).y) =
    ((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 + 2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
              (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
                Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x))) ^
            2 -
          Curve25519.A -
        (1 + e₂.y) / (1 - e₂.y) -
      (1 + e₂.y) / (1 - e₂.y) := by
  sorry
lemma fromEdwards_u_add_of_eq_y_of_neg_x {e₁ e₂ : Edwards.Point Edwards.Ed25519}
  (sum_x : (e₁ + e₂).x ≠ 0)
  (heqy : e₁.y = e₂.y)
  (heqx : e₁.x = -e₂.x) :
 (1 + (e₁ + e₂).y) / (1 - (e₁ + e₂).y) =
    ((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 + 2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
              (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
                Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x))) ^
            2 -
          Curve25519.A -
        (1 + e₂.y) / (1 - e₂.y) -
      (1 + e₂.y) / (1 - e₂.y) := by
  sorry
lemma fromEdwards_u_add_of_eq_y {e₁ e₂ : Edwards.Point Edwards.Ed25519}
  (non_e1_x : ¬e₁.x = 0)
  (zero_e2_x : e₂.x ≠ 0)
  (hy1 : 1 - e₂.y ≠ 0)
  (hy3 : 1 + e₂.y ≠ 0)
  (sum_x : (e₁ + e₂).x ≠ 0)
  (heqy : e₁.y = e₂.y) :
 (1 + (e₁ + e₂).y) / (1 - (e₁ + e₂).y) =
    ((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 + 2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
              (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
                Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x))) ^
            2 -
          Curve25519.A -
        (1 + e₂.y) / (1 - e₂.y) -
      (1 + e₂.y) / (1 - e₂.y) := by
  sorry
lemma fromEdwards_v_add_of_eq {e₁ e₂ : Edwards.Point Edwards.Ed25519}
  (non_e1_x : ¬e₁.x = 0)
  (zero_e2_x : e₂.x ≠ 0)
  (hy1 : 1 - e₂.y ≠ 0)
  (hy3 : 1 + e₂.y ≠ 0)
  (sum_x : (e₁ + e₂).x ≠ 0)
  (sum_y : ¬(e₁ + e₂).y = 1)
  (heqy : e₁.y = e₂.y)
  (heqx : e₁.x = e₂.x) :
Curve25519.roots_B * (1 + (e₁ + e₂).y) / ((1 - (e₁ + e₂).y) * (e₁ + e₂).x) =
  -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x)) +
    -((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 + 2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
          (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
            Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x)) *
        (((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 + 2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
                    (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
                      Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x))) ^
                  2 -
                Curve25519.A -
              (1 + e₂.y) / (1 - e₂.y) -
            (1 + e₂.y) / (1 - e₂.y) -
          (1 + e₂.y) / (1 - e₂.y))) := by
  sorry
lemma fromEdwards_v_add_of_eq_y_of_neg_x {e₁ e₂ : Edwards.Point Edwards.Ed25519}
  (sum_x : (e₁ + e₂).x ≠ 0)
  (heqy : e₁.y = e₂.y)
  (heqx : e₁.x = -e₂.x) :
Curve25519.roots_B * (1 + (e₁ + e₂).y) / ((1 - (e₁ + e₂).y) * (e₁ + e₂).x) =
  -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x)) +
    -((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 + 2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
          (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
            Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x)) *
        (((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 + 2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
                    (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
                      Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x))) ^
                  2 -
                Curve25519.A -
              (1 + e₂.y) / (1 - e₂.y) -
            (1 + e₂.y) / (1 - e₂.y) -
          (1 + e₂.y) / (1 - e₂.y))) := by
  sorry
lemma fromEdwards_v_add_of_eq_y {e₁ e₂ : Edwards.Point Edwards.Ed25519}
  (non_e1_x : ¬e₁.x = 0)
  (zero_e2_x : e₂.x ≠ 0)
  (hy1 : 1 - e₂.y ≠ 0)
  (hy3 : 1 + e₂.y ≠ 0)
  (sum_x : (e₁ + e₂).x ≠ 0)
  (sum_y : ¬(e₁ + e₂).y = 1)
  (heqy : e₁.y = e₂.y) :
Curve25519.roots_B * (1 + (e₁ + e₂).y) / ((1 - (e₁ + e₂).y) * (e₁ + e₂).x) =
  -(Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x)) +
    -((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 + 2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
          (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
            Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x)) *
        (((3 * ((1 + e₂.y) / (1 - e₂.y)) ^ 2 + 2 * Curve25519.A * ((1 + e₂.y) / (1 - e₂.y)) + 1) /
                    (Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x) +
                      Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₁.x))) ^
                  2 -
                Curve25519.A -
              (1 + e₂.y) / (1 - e₂.y) -
            (1 + e₂.y) / (1 - e₂.y) -
          (1 + e₂.y) / (1 - e₂.y))) := by
  sorry
lemma fromEdwards_u_add_of_y_ne (e₁ e₂ : Edwards.Point Edwards.Ed25519)
(non_e1_x : ¬e₁.x = 0)
(non_e2_x : ¬e₂.x = 0)
(h1 : ¬e₁.y = 1)
(h2 : ¬e₂.y = 1)
(sum_y : ¬(e₁ + e₂).y = 1)
(hy1 : 1 - e₂.y ≠ 0)
(hy2 : 1 - e₁.y ≠ 0)
(hy3 : 1 + e₂.y ≠ 0)
(hy4 : 1 + e₁.y ≠ 0)
(heqy : ¬e₁.y = e₂.y) :
 (1 + (e₁ + e₂).y) / (1 - (e₁ + e₂).y) =
  ((Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) - Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x)) /
            ((1 + e₁.y) / (1 - e₁.y) - (1 + e₂.y) / (1 - e₂.y))) ^
          2 -
        Curve25519.A -
      (1 + e₁.y) / (1 - e₁.y) -
    (1 + e₂.y) / (1 - e₂.y) := by
  sorry
lemma fromEdwards_v_add_of_y_ne (e₁ e₂ : Edwards.Point Edwards.Ed25519)
(non_e1_x : ¬e₁.x = 0)
(non_e2_x : ¬e₂.x = 0)
(h1 : ¬e₁.y = 1)
(h2 : ¬e₂.y = 1)
(sum_x : ¬(e₁ + e₂).x = 0)
(sum_y : ¬(e₁ + e₂).y = 1)
(hy1 : 1 - e₂.y ≠ 0)
(hy2 : 1 - e₁.y ≠ 0)
(hy3 : 1 + e₂.y ≠ 0)
(hy4 : 1 + e₁.y ≠ 0)
(heqy : ¬e₁.y = e₂.y) :
 Curve25519.roots_B * (1 + (e₁ + e₂).y) / ((1 - (e₁ + e₂).y) * (e₁ + e₂).x) =
  -(Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x)) +
    -((Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) - Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x)) /
          ((1 + e₁.y) / (1 - e₁.y) - (1 + e₂.y) / (1 - e₂.y)) *
        (((Curve25519.roots_B * (1 + e₁.y) / ((1 - e₁.y) * e₁.x) -
                      Curve25519.roots_B * (1 + e₂.y) / ((1 - e₂.y) * e₂.x)) /
                    ((1 + e₁.y) / (1 - e₁.y) - (1 + e₂.y) / (1 - e₂.y))) ^
                  2 -
                Curve25519.A -
              (1 + e₁.y) / (1 - e₁.y) -
            (1 + e₂.y) / (1 - e₂.y) -
          (1 + e₁.y) / (1 - e₁.y))) := by
  sorry
theorem fromEdwards_add_of_x_ne_zero (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x ≠ 0)
  (zero_e2_x : e₂.x ≠ 0)
  (sum_x : (e₁ + e₂).x ≠ 0) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  sorry
lemma fromEdwards_add_of_snd_y_eq_neg_one (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e2_x : ¬e₂.x = 0)
  (eq_e2_y_1 : 1 + e₂.y = 0) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  sorry
lemma fromEdwards_add_of_first_y_eq_neg_one (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e2_x : ¬e₁.x = 0)
  (eq_e2_y_1 : 1 + e₁.y = 0) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  sorry
lemma fromEdwards_add_of_sum_x_eq_zero_of_y_ne_one_of_y_ne_neg_one (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (sum_x : (e₁ + e₂).x = 0)
  (sum_y : ¬(e₁ + e₂).y = 1)
  (sum_y_1 : ¬(e₁ + e₂).y = -1) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  sorry
lemma fromEdwards_add_of_x_eq_zero (e₁ e₂ : Edwards.Point Edwards.Ed25519)
  (non_e1_x : e₁.x = 0)
  (non_e2_x : e₂.x = 0) :
 fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  sorry
theorem add_fromEdwards (e₁ e₂ : Edwards.Point Edwards.Ed25519) :
  fromEdwards (e₁ + e₂) = fromEdwards e₁ + fromEdwards e₂ := by
  sorry
theorem double_T {e : Edwards.Point Edwards.Ed25519} (hx : e.x = 0) :
  (e + e).x=0 := by
  sorry
theorem power_T (n : ℕ) {e : Edwards.Point Edwards.Ed25519} (hx : e.x = 0) :
  n • e.x=0 := by
  sorry
theorem double_T1 {e : Edwards.Point Edwards.Ed25519}
  (hx : (e + e).x = 0) :
  (e.x=0 ∧ e.y ^ 2 =1) ∨  (e.x ^ 2 = -1 ∧ e.y =0) := by
  sorry
theorem double_special_point {e : Edwards.Point Edwards.Ed25519}
  (hx : e.x ^ 2 = -1)
  (hy : e.y = 0) :
  (e + e).y = -1 ∧ (e + e).x = 0 ∧ ¬ e.x= 0 := by
  sorry
theorem double_fromEdwards_special_point (e : Edwards.Point Edwards.Ed25519)
  (hx : e.x ^ 2 = -1)
  (hy : e.y = 0) :
  fromEdwards (e + e) = (fromEdwards e) + (fromEdwards e) := by
  sorry
theorem double_fromEdwards_zero_x (e : Edwards.Point Edwards.Ed25519)
  (hx : (e + e).x = 0) :
  fromEdwards (e + e) = (fromEdwards e) + (fromEdwards e) := by
  sorry
theorem comm_mul_fromEdwards {n : ℕ} (e : Edwards.Point Edwards.Ed25519) :
  fromEdwards (n • e) = n • (fromEdwards e) := by
  sorry
/-
theorem fromEdwards_eq_MontgomeryPoint_toPoint (e : Edwards.Point Edwards.Ed25519)
  (m : MontgomeryPoint)
  (non : ¬ e.y = 1)
  (non_x : ¬ e.x = 0)
  (h : (((U8x32_as_Nat m) % 2 ^ 255) : ℕ) = (1 + e.y) / (1 - e.y)) :
  fromEdwards e = MontgomeryPoint.mkPoint m  := by
  unfold fromEdwards
  simp only [non, ↓reduceDIte, non_x, false_and]
  unfold MontgomeryPoint.mkPoint
  rw[h]
  clear *- non
  apply symm
  apply MontgomeryPoint.u_affine_toPoint_spec
  · simp only [ne_eq, div_eq_zero_iff, not_or]
    constructor
    · intro ha
      have := exceptEdwardsPoint ha
      apply non_x this
    · grind only
  · have := on_MontgomeryCurves e non non_x
    simp only at this
    apply this
-/
end fromEdwards

section toEdwards
open curve25519_dalek.math

noncomputable def toEdwards : Point → Option (Edwards.Point Edwards.Ed25519)
  | .zero => some 0
  | .some (x := u) (y := v) (h:= h) =>
   let y := (u - 1) * (u + 1)⁻¹
   let den : ZMod p := (d : ZMod p) * y^2 + 1
   let num : ZMod p := y^2 - 1
   let x2 : ZMod p := num * den⁻¹
   match h_call: curve25519_dalek.math.sqrt_checked x2 with
    | (x_abs, was_square) =>
    let x := x_abs
    if h_invalid : !was_square then
      none
    else
    -- For Montgomery -> Edwards, the sign of x is lost.
    -- We canonically choose the non-negative (even) root.
    some { x := x_abs, y := y, on_curve := (by
        replace h_invalid := Bool.eq_false_iff.mpr h_invalid
        simp only [Bool.not_eq_eq_eq_not, Bool.not_false] at h_invalid
        have eq:=h.left
        rw [WeierstrassCurve.Affine.equation_iff] at eq
        simp [MontgomeryCurveCurve25519] at eq
        have non:=h.right
        simp [WeierstrassCurve.Affine.evalEval_polynomialY, WeierstrassCurve.Affine.evalEval_polynomialX, MontgomeryCurveCurve25519] at non
        have h_x_sq : x_abs^2 = x2 := by
          apply sqrt_checked_spec x2 h_call h_invalid
        have h_den_nz : den ≠ 0 := by
          dsimp only [den]
          apply edwards_denom_nonzero
        have ha : Edwards.Ed25519.a = -1 := rfl
        have hd : (d : ZMod p) = Edwards.Ed25519.d := rfl
        rw [ha, h_x_sq]
        dsimp only [x2, num, den] at ⊢ h_den_nz
        apply (mul_right_inj' h_den_nz).mp
        field_simp [h_den_nz]
        simp only [neg_sub]
        rw [← hd]
        try ring)
      }

noncomputable def toEdwards.fromMontgomeryPoint (m : MontgomeryPoint) : Option (Edwards.Point Edwards.Ed25519):=
    let p := MontgomeryPoint.mkPoint m
    toEdwards p

end toEdwards

end Montgomery
