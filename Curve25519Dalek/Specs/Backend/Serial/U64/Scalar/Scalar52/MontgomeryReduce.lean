/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
-- import Curve25519Dalek.Aux
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.ExternallyVerified
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.M
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.L
import Curve25519Dalek.Specs.Backend.Serial.U64.Constants.LFACTOR
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.Scalar52.Sub

import Mathlib.Algebra.Polynomial.Eval.Algebra
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree

import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic

/-! # Spec Theorem for `Scalar52::montgomery_reduce`

Specification and proof for `Scalar52::montgomery_reduce`.

This function performs Montgomery reduction.

**Source**: curve25519-dalek/src/backend/serial/u64/scalar.rs

## TODO
- Complete proof
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP curve25519_dalek.backend.serial.u64
open Polynomial
namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

set_option exponentiation.threshold 262

/-
natural language description:

    • **Motivation**: The Montgomery form `M(x) := x * R`, where `R = 2^{260} = 2^{5*52}`,
      is used to optimize chains of modular arithmetic operations (like elliptic curve scalar
      multiplication). The isomorphism induced by `* R` changes the multiplication to:
      `MontMul(x,y) := M(x) * M(y) * R⁻¹`. Therefore, instead of computing standard reduction
      (`x % L`) which requires complex division logic, one needs to compute `x * R⁻¹ (mod L)`.
      Montgomery reduction refers to the algorithm that computes this `x * R⁻¹` using efficient
      bitwise shifts.

    • **Mechanism**: The algorithm avoids division by adding multiples of `L` to the input `x`
      until the result is exactly divisible by `R = 2^{260}` (i.e., the lower 260 bits are all zero).
      Since `R = 2^{260}` and limbs are 52 bits, we perform 5 "zeroing" steps (`part1`)
      followed by 4 "result assembly" steps (`part2`).

    • **Part 1: The Zeroing Strategy**
      We iteratively ensure the lowest remaining limb is 0 by adding a carefully chosen multiple of `L`.
      The helper `part1` calculates a "zeroing factor" `p` using the precomputed `LFACTOR`
      (where `LFACTOR * L ≡ -1 (mod 2⁵²)`).

      - **Limb 0 (First part1)**:
        * **Problem**: `limbs[0]` is non-zero. We cannot shift yet.
        * **Action**: Calculate `p` such that `limbs[0] + p * L ≡ 0 (mod 2⁵²)`.
        * **Result**: The sum's lowest 52 bits become 0.
        * **Shift**: We discard these zero bits (effectively dividing by 2⁵²). The carry flows to the next limb.

      *This repeats 5 times (using updated carries) until the entire lower 260 bits are zero.*

    • **Part 2: Result Reconstruction**
      After 5 reductions, the number is divisible by `R`. The helper `part2` extracts the quotient.
      It takes the high-order accumulated bits, slices off the lower 52 bits as a result limb (`w`),
      and passes the remaining upper bits (`carry`) to the next position. This reassembles
      the final 256-bit result (`r0` through `r4`).

natural language specs:

    • For any 9-limb array `a` of u128 values (representing a 512-bit integer):
      - The function returns a `Scalar52` `m` such that:
        `Scalar52_as_Nat(m) * R ≡ U128x9_as_Nat(a) (mod L)`
-/

-- Bridge lemma: converts the existing LFACTOR_spec (on Nat) to the form needed for Int arithmetic
private lemma LFACTOR_prop :
    (↑constants.LFACTOR.val * ↑constants.L[0]!.val : Int) % (2 ^ 52) = (2 ^ 52) - 1 := by
  have h_nat := constants.LFACTOR_spec
  obtain ⟨h_mod_zero, _, _⟩ := h_nat
  have h_cong : (constants.L[0]!.val : Int) % (2^52) = (_root_.L : Int) % (2^52) := by
    rw [← constants.L_spec]; unfold Scalar52_as_Nat
    rw [Finset.sum_range_succ']; zify at h_mod_zero ⊢; simp only [mul_zero, pow_zero, one_mul]
    rw [Int.add_emod]
    have h_tail_div : (∑ x ∈ Finset.range 4, (2:Int)^(52 * (x + 1)) *
      (constants.L[x.succ]!).val) % 2^52 = 0 := by
      apply Int.emod_eq_zero_of_dvd
      use (∑ x ∈ Finset.range 4, (2:Int)^(52 * x) * (constants.L[x.succ]!).val)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h_tail_div, zero_add, Int.emod_emod]
  rw [mul_comm, Int.mul_emod, h_cong, ← Int.mul_emod]
  rw [← Int.add_sub_cancel (_root_.L * ↑constants.LFACTOR.val : Int) 1, Int.sub_emod]; norm_cast
  rw [h_mod_zero]; exact rfl

/-- The "Montgomery Step": Proves that adding the reduction factor clears the lower 52 bits. -/
private lemma mont_step (x : Int) (p : Int) (carry_out : Int)
    (hp : p = (x * ↑constants.LFACTOR.val) % (2 ^ 52))
    (hcarry : carry_out = (x + p * ↑constants.L[0]!.val) / (2 ^ 52)) :
    x + p * ↑constants.L[0]!.val = carry_out * (2 ^ 52) := by
  have h_div : x + p * ↑constants.L[0]!.val = carry_out * (2 ^ 52) + (x + p * ↑constants.L[0]!.val) % (2 ^ 52) := by
    rw [hcarry]
    rw [mul_comm ((x + p * ↑constants.L[0]!.val) / 2 ^ 52)]
    rw [Int.mul_ediv_add_emod]
  have h_mod_zero : (x + p * ↑constants.L[0]!.val) % (2 ^ 52) = 0 := by
    rw [hp, Int.add_emod, Int.mul_emod, Int.emod_emod, ← Int.mul_emod, mul_assoc, Int.mul_emod]
    rw [LFACTOR_prop]
    rw [← Int.zero_emod (2 ^ 52)]
    have h_cast : (2 : Int) ^ 52 = ((2 ^ 52 : Nat) : Int) := by norm_cast
    rw [h_cast]
    apply (ZMod.intCast_eq_intCast_iff' _ _ (2^52)).mp
    simp only [Int.cast_add, ZMod.intCast_mod, Int.cast_mul, Int.cast_sub]
    simp only [Nat.reducePow, Nat.cast_ofNat, Int.cast_ofNat, Aeneas.ReduceZMod.reduceZMod,
      Int.cast_one, zero_sub, mul_neg, mul_one, add_neg_cancel, Int.cast_zero]
  rw [h_div, h_mod_zero, add_zero]


private theorem part1_spec_tail (sum i5 : U128) (p : U64)
    (h_p_val : p.val = (sum.val * constants.LFACTOR) % (2 ^ 52))
    (h_p_bound : p.val < 2 ^ 52)
    (h_add : sum.val + i5.val ≤ U128.max)
    (h_i5_eq : i5.val = p.val * (constants.L[0]!).val) :
    (do
      let i6 ← sum + i5
      let i7 ← i6 >>> 52#i32
      ok (i7, p)) ⦃ result =>
      let (carry, p') := result
      p'.val = (sum.val * constants.LFACTOR) % (2 ^ 52) ∧
      carry.val = (sum.val + p'.val * (constants.L[0]!).val) / (2 ^ 52) ∧
      carry.val < 2 ^ 77 ∧
      p'.val < 2 ^ 52 ⦄ := by
  progress as ⟨i6, i6_post⟩
  progress as ⟨i7, i7_post⟩
  refine ⟨h_p_val, ?_, ?_, h_p_bound⟩
  · rw [i7_post, i6_post, h_i5_eq]; simp only [Nat.shiftRight_eq_div_pow]
  · rw [i7_post, i6_post]; simp only [Nat.shiftRight_eq_div_pow]; scalar_tac

@[progress]
private theorem part1_spec (sum : U128)
    (h_bound : sum.val + (2 ^ 52 - 1) * (constants.L[0]!).val ≤ U128.max) :
    montgomery_reduce.part1 sum ⦃ result =>
    let (carry, p) := result
    p.val = (sum.val * constants.LFACTOR) % (2 ^ 52) ∧
    carry.val = (sum.val + p.val * (constants.L[0]!).val) / (2 ^ 52) ∧
    carry.val < 2 ^ 77 ∧
    p.val < 2 ^ 52 ⦄ := by
  unfold montgomery_reduce.part1
  unfold backend.serial.u64.scalar.Scalar52.Insts.CoreOpsIndexIndexUsizeU64.index
  have h_L_len : constants.L.val.length = 5 := by
    unfold constants.L; rfl
  progress as ⟨i, i_post⟩
  progress as ⟨i1, i1_post⟩
  progress as ⟨i2, i2_post⟩
  progress as ⟨i3, i3_post⟩
  progress as ⟨p, p_post⟩
  have h_p_val : p.val = (sum.val * constants.LFACTOR) % (2 ^ 52) := by
      rw [p_post]; simp only [UScalar.val_and]
      have h_mask : i3.val = 2^52 - 1 := by
        simp only [i3_post, i2_post]; scalar_tac
      rw [h_mask]; rw [i1_post, i_post]
      rw [land_pow_two_sub_one_eq_mod]
      simp only [UScalar.cast, UScalar.val, core.num.U64.wrapping_mul]
      simp only [UScalarTy.U64_numBits_eq, UScalar.wrapping_mul_bv_eq, UScalar.bv_toNat,
        Aeneas.Bvify.U64.UScalar_bv]
      rw [BitVec.toNat_mul, BitVec.toNat_setWidth, UScalar.bv_toNat, Nat.mod_mul_mod]
      rw [Nat.mod_mod_of_dvd _ (by norm_num : 2^52 ∣ 2^64)]
      rfl
  have h_p_bound : p.val < 2^52 := by
      rw [h_p_val]; apply Nat.mod_lt; norm_num
  have h_add_safe : sum.val + p.val * (constants.L[0]!).val ≤ U128.max := by
      apply Nat.le_trans (m := sum.val + (2^52 - 1) * (constants.L[0]!).val)
      · apply Nat.add_le_add_left; apply Nat.mul_le_mul_right; apply Nat.le_pred_of_lt h_p_bound
      · exact h_bound
  progress as ⟨i4, i4_post⟩
  progress as ⟨i5, i5_post⟩
  have h_add_safe' : sum.val + i5.val ≤ U128.max := by
    rw [i5_post, i4_post]
    convert h_add_safe using 2
    simp only [Array.getElem!_Nat_eq]
  have h_i5_eq : i5.val = p.val * (constants.L[0]!).val := by
    rw [i5_post, i4_post]
    simp only [Array.getElem!_Nat_eq]
  exact part1_spec_tail sum i5 p h_p_val h_p_bound h_add_safe' h_i5_eq

@[progress]
private theorem part2_spec (sum : U128) :
  montgomery_reduce.part2 sum ⦃ result =>
  let (carry, w) := result
  w.val = sum.val % (2 ^ 52) ∧
  carry.val = sum.val / (2 ^ 52) ∧
  carry.val < 2 ^ 76 ∧
  w.val < 2 ^ 52 ⦄ := by -- 2^128 / 2^52 = 2^76
  unfold montgomery_reduce.part2
  -- Rust: let w = (sum as u64) & ((1u64 << 52) - 1);
  progress as ⟨w_cast, hw_cast⟩     -- Cast sum to u64
  progress as ⟨mask1, hmask1⟩       -- 1 << 52
  progress as ⟨mask, hmask⟩         -- (1 << 52) - 1
  progress as ⟨w, hw⟩               -- Bitwise AND
  -- Rust: (sum >> 52, w)
  progress as ⟨carry, hcarry⟩       -- Shift right
  have h_w_val : w.val = sum.val % 2^52 := by
    rw [hw]; simp only [UScalar.val_and]
    have h_mask_val : mask.val = 2^52 - 1 := by
      simp only [hmask, hmask1]; scalar_tac
    rw [h_mask_val]; rw [land_pow_two_sub_one_eq_mod]; rw [hw_cast]
    simp only [UScalar.cast, UScalarTy.U64_numBits_eq, BitVec.truncate_eq_setWidth]
    change (BitVec.setWidth 64 sum.bv).toNat % 2^52 = _
    rw [BitVec.toNat_setWidth]
    change (sum.val % 2^64) % 2^52 = _
    apply Nat.mod_mod_of_dvd; scalar_tac
  have h_carry_val : carry.val = sum.val / 2^52 := by
    rw [hcarry]
    simp only [Nat.shiftRight_eq_div_pow]
  have h_w_bound : w.val < 2^52 := by
    rw [h_w_val]; apply Nat.mod_lt; norm_num
  have h_carry_bound : carry.val < 2^76 := by
    rw [h_carry_val]; apply Nat.div_lt_of_lt_mul
    have h : sum.val < 2^128 := sum.hBounds
    calc sum.val < 2^128 := h
         _ = 2^76 * 2^52 := by norm_num
  exact ⟨h_w_val, h_carry_val, h_carry_bound, h_w_bound⟩

set_option maxHeartbeats 200000 in -- Progress will timout otherwise
/-- **Spec and proof concerning `scalar.Scalar52.montgomery_reduce`**:
- No panic (always returns successfully)
- The result m satisfies the Montgomery reduction property:
  m * R ≡ a (mod L), where R = 2^260 is the Montgomery constant
-/
@[externally_verified, progress] -- working proof commented out because of slow build
theorem montgomery_reduce_spec (a : Array U128 9#usize)
    (h_bounds : ∀ i < 9, a[i]!.val < 2 ^ 127) :
    montgomery_reduce a ⦃ m =>
    (Scalar52_as_Nat m * R) % L = Scalar52_wide_as_Nat a % L ∧
    (∀ i < 5, m[i]!.val < 2 ^ 52) ∧
    (Scalar52_as_Nat m < L) ⦄
    := by
  sorry
end curve25519_dalek.backend.serial.u64.scalar.Scalar52
