/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Alessandro D'Angelo
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Square
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Neg
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect
import Curve25519Dalek.Specs.Field.FieldElement51.SqrtRatioi
import Curve25519Dalek.Specs.Field.FieldElement51.InvSqrt
import Curve25519Dalek.Specs.Field.FieldElement51.IsNegative
import Curve25519Dalek.Specs.Field.FieldElement51.IsZero
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.EDWARDS_D
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE

/-! # Spec Theorem for `ristretto.decompress.step_2`

Specification and proof for `ristretto.decompress.step_2`.

This function performs the second step of Ristretto decompression, computing
the affine coordinates (x, y) of a point on the Edwards curve from the field element s, then
outputs extended Edwards coordinates (x, y, 1, xy)

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Edwards Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field
open curve25519_dalek.math curve25519_dalek.ristretto
namespace curve25519_dalek.ristretto.decompress

/-- Standalone on-curve proof for decompression, extracted to avoid heartbeat
    timeout in the large proof context of step_2_spec. -/
private lemma on_curve_from_decompression {F : Type*} [Field F]
    (a d s I u1 u2 u7 : F)
    (ha : a = -1)
    (hu1 : u1 = 1 - s ^ 2)
    (hu2 : u2 = 1 + s ^ 2)
    (hu7 : u7 = -d * u1 ^ 2 - u2 ^ 2)
    (hI : I ^ 2 * (u7 * u2 ^ 2) = 1) :
    a * (2 * s * I * u2) ^ 2 + (u1 * (I ^ 2 * u2 * u7)) ^ 2 =
    1 + d * (2 * s * I * u2) ^ 2 * (u1 * (I ^ 2 * u2 * u7)) ^ 2 := by
  have h := decompress_helper a d s I u1 u2 u7 ha
    (by rw [hu1, ha]; ring) (by rw [hu2, ha]; ring)
    (by rw [hu7, ha]; ring) hI
  dsimp only at h
  linear_combination h

/-- Extract coordinates from a RistrettoPoint.toPoint with Z = ONE.
    Factored out to avoid whnf timeout from toPoint reduction in large contexts. -/
private lemma toPoint_coords {x y z t : FieldElement51}
    (h : edwards.EdwardsPoint.IsValid { X := x, Y := y, Z := z, T := t })
    (hz : z.toField = (1 : CurveField))
    {P : Point Ed25519}
    (h_pt : RistrettoPoint.toPoint { X := x, Y := y, Z := z, T := t } = P) :
    P.x = x.toField ∧ P.y = y.toField := by
  have hPxy := edwards.EdwardsPoint.toPoint_of_isValid h
  unfold RistrettoPoint.toPoint at h_pt
  constructor
  · rw [← h_pt, hPxy.1, hz, div_one]
  · rw [← h_pt, hPxy.2, hz, div_one]

/-- Combine P.x*P.y = t.toField with is_negative t.toField = false.
    Extracted to avoid whnf timeout from toField/is_negative reduction in large contexts. -/
private lemma is_negative_Pxy_false {x1 y t : FieldElement51} {P : Point Ed25519}
    {c : subtle.Choice}
    (hPx : P.x = x1.toField) (hPy : P.y = y.toField)
    (ht : t.toField = x1.toField * y.toField)
    (h_c : c.val = 0#u8)
    (h_post : c.val = 1#u8 ↔ Field51_as_Nat t % p % 2 = 1) :
    is_negative (P.x * P.y) = false := by
  have h1 : P.x * P.y = t.toField := by rw [hPx, hPy, ← ht]
  rw [h1]
  simp only [is_negative, FieldElement51.toField, ZMod.val_natCast,
    beq_eq_false_iff_ne]
  intro h
  exact absurd (h_post.mpr h) (by rw [h_c]; decide)

/-- P.y ≠ 0 from c1.val = 0 and the is_zero postcondition.
    Extracted to avoid timeout from ZMod unfolding in large contexts. -/
private lemma Py_ne_zero {y : FieldElement51} {P : Point Ed25519} {c1 : subtle.Choice}
    (hPy : P.y = y.toField)
    (h_c1 : c1.val = 0#u8)
    (h_post : c1.val = 1#u8 ↔ Field51_as_Nat y % p = 0) :
    P.y ≠ 0 := by
  rw [hPy]
  simp only [FieldElement51.toField, ne_eq, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
  intro h
  exact absurd (h_post.mpr h) (by rw [h_c1]; decide)


/-- Wrapper for `decompress_step2_2` with the algebraic forms used in step_2_spec.
    Extracted to avoid ring normalization timeouts in the large proof context. -/
private lemma decompress_step2_backward (s I u1 u2 u7 : ZMod p)
    (hu1 : u1 = 1 - s ^ 2)
    (hu2 : u2 = 1 + s ^ 2)
    (hu7 : u7 = -Ed25519.d * u1 ^ 2 - u2 ^ 2)
    (hI : I ^ 2 * (u7 * u2 ^ 2) = 1)
    (pt : Point Ed25519)
    (h_neg : is_negative (pt.x * pt.y) = false)
    (h_y_ne : pt.y ≠ 0)
    (hx : pt.x = abs_edwards (2 * s * I * u2))
    (hy : pt.y = u1 * (I ^ 2 * u2 * u7)) :
    decompress_step2 s = some pt := by
  have hEd : Ed25519.d = (↑d : ZMod p) := rfl
  have h_u1_eq : (1 + a_val * s ^ 2) = u1 := by rw [hu1, a_val]; ring
  have h_u2_eq : (1 - a_val * s ^ 2) = u2 := by rw [hu2, a_val]; ring
  have h_v_eq : a_val * (↑d : ZMod p) * u1 ^ 2 - u2 ^ 2 = u7 := by
    rw [hu7, hEd, a_val]; ring
  apply decompress_step2_2 s pt I
  · rw [h_u1_eq, h_u2_eq, h_v_eq]; exact hI
  · exact h_neg
  · exact h_y_ne
  · rw [hx]; congr 1; rw [h_u2_eq]; ring
  · rw [h_u1_eq, h_u2_eq, h_v_eq, hy]; ring

/-- Forward wrapper for `decompress_step2_1`, converting a_val form to Ed25519.d form.
    Given decompress_step2 succeeds, we get IsSquare W, W ≠ 0, validation passes,
    and for any I with I²·W = 1 the point coordinates are determined.
    Proof bridges a_val = -1 and Ed25519.d = ↑d to decompress_step2_1. -/
private lemma decompress_step2_forward (s : ZMod p) (P : Point Ed25519)
    (h : decompress_step2 s = some P)
    (u1 u2 v W : ZMod p)
    (hu1 : u1 = 1 - s ^ 2)
    (hu2 : u2 = 1 + s ^ 2)
    (hv : v = -Ed25519.d * u1 ^ 2 - u2 ^ 2)
    (hW : W = v * u2 ^ 2) :
    IsSquare W ∧ W ≠ 0 ∧
    is_negative (P.x * P.y) = false ∧
    P.y ≠ 0 ∧
    (∀ I : ZMod p, I ^ 2 * W = 1 →
      P.x = abs_edwards (2 * s * I * u2) ∧
      P.y = u1 * (I ^ 2 * u2 * v)) := by
  have h_data := decompress_step2_1 s P h
  obtain ⟨h_sq', h_ne', h_neg', h_y_ne', h_Px', h_Py'⟩ := h_data
  -- Bridge between a_val form and Ed25519.d form
  have hEd : Ed25519.d = (↑d : ZMod p) := rfl
  have hu1' : (1 + a_val * s ^ 2) = u1 := by rw [hu1, a_val]; ring
  have hu2' : (1 - a_val * s ^ 2) = u2 := by rw [hu2, a_val]; ring
  have hv' : a_val * (↑d : CurveField) * (1 + a_val * s ^ 2) ^ 2 -
    (1 - a_val * s ^ 2) ^ 2 = v := by rw [hv, hEd, hu1, hu2, a_val]; ring
  have hW' : (a_val * (↑d : CurveField) * (1 + a_val * s ^ 2) ^ 2 -
    (1 - a_val * s ^ 2) ^ 2) * (1 - a_val * s ^ 2) ^ 2 = W := by
    rw [hW, hv, hEd, hu1, hu2, a_val]; ring
  -- Rewrite hypotheses to use u1, u2, v, W (order matters!)
  -- hW' first: replaces the full W-expression inside inv_sqrt_checked args
  rw [hW'] at h_sq' h_ne' h_neg' h_y_ne' h_Px' h_Py'
  -- hv' next: replaces the standalone v-expression (before hu1'/hu2' break it)
  rw [hv', hu1', hu2'] at h_neg' h_y_ne' h_Py'
  rw [hu2'] at h_Px'
  set I_math := (inv_sqrt_checked W).1 with hI_math_def
  -- Goals 1-4
  refine ⟨h_sq', h_ne', ?_, ?_, ?_⟩
  · -- is_negative (P.x * P.y) = false
    rw [h_Px', h_Py']; exact h_neg'
  · -- P.y ≠ 0
    rw [h_Py']; exact h_y_ne'
  · -- ∀ I, I^2 * W = 1 → coordinates match
    intro I hI_sq
    -- Get I_math^2 * W = 1 (uses combined lemma to avoid maxRecDepth)
    have hI_math_sq : I_math ^ 2 * W = 1 := inv_sqrt_checked_sq_mul W h_sq' h_ne'
    -- I^2 = I_math^2
    have hI_sq_eq : I ^ 2 = I_math ^ 2 :=
      mul_right_cancel₀ h_ne' (by rw [hI_sq, hI_math_sq])
    constructor
    · -- P.x = abs_edwards (2 * s * I * u2)
      rw [h_Px']
      -- Prove squares are equal via separate ring lemmas (avoids ring_nf unfolding I_math)
      have h_x_sq : (2 * s * I * u2) ^ 2 = (2 * s * (I_math * u2)) ^ 2 := by
        have h1 : (2 * s * I * u2) ^ 2 = 4 * s ^ 2 * I ^ 2 * u2 ^ 2 := by ring
        have h2 : (2 * s * (I_math * u2)) ^ 2 = 4 * s ^ 2 * I_math ^ 2 * u2 ^ 2 := by ring
        rw [h1, h2, hI_sq_eq]
      exact (abs_edwards_eq_of_sq_eq h_x_sq).symm
    · -- P.y = u1 * (I^2 * u2 * v)
      rw [h_Py']
      -- Rewrite I_math * (I_math * u2) * v to I_math^2 * u2 * v, then to I^2 * u2 * v
      have h1 : I_math * (I_math * u2) * v = I_math ^ 2 * u2 * v := by ring
      rw [h1, ← hI_sq_eq]

/-
natural language description:

    • Takes a field element s as input (from step_1)
    • Computes ss = s²
    • Computes u1 = 1 - ss
    • Computes u2 = 1 + ss
    • Computes u2_sqr = u2²
    • Computes v = (-EDWARDS_D) · u1² - u2²
    • Computes I = invsqrt(v · u2²), obtaining (ok1, I) where ok1 indicates if the inverse square root exists
    • Computes Dx = I · u2
    • Computes Dy = I · Dx · v
    • Computes x = 2s · Dx
    • Conditionally negates x if x is negative, producing x1
    • Computes y = u1 · Dy
    • Computes t = x1 · y (the extended coordinate)
    • Checks if t is negative (stored in c)
    • Checks if y is zero (stored in c1)
    • Returns a tuple containing:
        - ok1: Choice indicating whether the inverse square root computation succeeded
        - c: Choice indicating whether t is negative
        - c1: Choice indicating whether y is zero
        - A RistrettoPoint with coordinates (X=x1, Y=y, Z=1, T=t) in extended twisted Edwards form

    This is the second step in Ristretto decompression. It computes the point coordinates
    from the field element s, performing the inverse of the Ristretto encoding map.
    The three Choice values (ok1, c, c1) are used in the full decompress function to validate
    that the decompression is valid.

natural language specs:

    • The function always succeeds (no panic) for any valid field element s
    • ok1 is true iff the inverse square root of w := v · u2² exists,
      where v = (-EDWARDS_D) · u1² - u2², u1 = 1 - s², u2 = 1 + s².
      The function called in step_2 is `invsqrt(w)`, which computes
      r = 1/√w. For 1/√w to exist we need w ≠ 0 (so that 1/w is
      defined) and w to be a quadratic residue (so that √w exists).
      Equivalently, `invsqrt` tests whether r² · w ≡ 1 (mod p) has a
      solution. When w = 0, r² · 0 = 0 ≠ 1, so no solution exists and
      ok1 = 0. Since Mathlib's `IsSquare 0 = True` (0 = 0²), the spec
      requires the conjunct `w ≠ 0` alongside `IsSquare w`.
    • c is true if and only if t is negative, where t = x1 · y is the T coordinate of the output point
    • c1 is true if and only if y = 0
    • The output point pt is a valid RistrettoPoint when ok1 = 1, c = 0, and c1 = 0 (all checks pass)
-/


set_option maxHeartbeats 400000 in -- increased for progress* through many sub-calls
/-- **Spec for `step_2`**
Reflects the Rust implementation:
1.  Performs the algebraic lift (Elligator map) to compute a point `pt`.
2.  Computes validity flags `ok1` (square exists), `c` (non-negative T), `c1` (non-zero Y).

It proves:
1.  **Low-Level Correctness**: The flags correspond exactly to their mathematical definitions.
2.  **High-Level Correctness**: The function returns a result that matches `decompress_step2` **iff** the flags indicate success.

Namely:
    • The function always succeeds (no panic) for any valid field element `s`
    • ok1 is true if and only if the inverse square root of v · u2² exists
    • c is true if and only if t is negative
    • c1 is true if and only if y is zero
    • pt is a valid RistrettoPoint when ok1 = 1, c = 0, and c1 = 0
Moreover if the high-level function returns `some P`, then:
a) The Rust flags must be set to success (1, 0, 0)
b) The Rust point `pt` must match the mathematical point `P`
And conversely.
-/
@[progress]
theorem step_2_spec (s : backend.serial.u64.field.FieldElement51)
    (h_s : ∀ i < 5, s[i]!.val < 2 ^ 52) :
    step_2 s ⦃ (ok1, c, c1, pt) =>
    (let s_val := s.toField
     let u1 := 1 - s_val ^ 2
     let u2 := 1 + s_val ^ 2
     let v := (-Ed25519.d) * u1 ^ 2 - u2 ^ 2
     (ok1.val = 1#u8 ↔ (v * u2 ^ 2 ≠ 0 ∧ IsSquare (v * u2 ^ 2))) ∧
     (c.val = 1#u8 ↔ math.is_negative pt.T.toField) ∧
     (c1.val = 1#u8 ↔ pt.Y.toField = 0)) ∧
    (∀ (P : Point Ed25519), ristretto.decompress_step2 s.toField = some P ↔
      (ok1.val = 1#u8 ∧ c.val = 0#u8 ∧ c1.val = 0#u8 ∧ pt.toPoint = P)) ∧
    (ok1.val = 1#u8 ∧ c.val = 0#u8 ∧ c1.val = 0#u8 → RistrettoPoint.IsValid pt) ⦄ := by
  sorry
end curve25519_dalek.ristretto.decompress
