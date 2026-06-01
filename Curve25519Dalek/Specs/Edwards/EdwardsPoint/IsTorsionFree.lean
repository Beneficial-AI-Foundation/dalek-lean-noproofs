/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Edwards.Representation
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Mul
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.Identity
import Curve25519Dalek.Specs.Edwards.EdwardsPoint.CtEq
import Curve25519Dalek.Specs.Edwards.CompressedEdwardsY.Identity
import Curve25519Dalek.Specs.Constants.BASEPOINT_ORDER_PRIVATE
/-! # Spec Theorem for `EdwardsPoint::is_torsion_free`

Specification and proof for `EdwardsPoint::is_torsion_free`.

This function determines whether an Edwards point is "torsion-free", i.e., is contained
in the prime-order subgroup. It does so by multiplying the point by the basepoint order L
and checking whether the result is the identity element.

**Source**: curve25519-dalek/src/edwards.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP Edwards
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.edwards.EdwardsPoint

/-
natural language description:

• Determines whether an EdwardsPoint is in the prime-order subgroup (torsion-free)

• A point is torsion-free if multiplying it by the basepoint order L results in the identity element

• Equivalently, the point has no torsion component, i.e., it lies entirely in the
  prime-order subgroup of the Edwards curve

natural language specs:

• The function always succeeds (no panic)
• Returns `true` if and only if the point is in the prime-order subgroup
• Equivalently, returns `true` iff multiplying by the basepoint order L yields the identity element
-/

private lemma field51_limb_le_of_sum_eq_zero {f : backend.serial.u64.field.FieldElement51}
    (h : Field51_as_Nat f = 0) : ∀ i < 5, (↑f)[i]!.val ≤ 2 ^ 53 := by
  simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
    Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton] at h
  intro i hi; interval_cases i <;> simp_all

private lemma field51_limb_le_of_sum_eq_one {f : backend.serial.u64.field.FieldElement51}
    (h : Field51_as_Nat f = 1) : ∀ i < 5, (↑f)[i]!.val ≤ 2 ^ 53 := by
  simp only [Field51_as_Nat, Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD,
    Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton] at h
  intro i hi; interval_cases i <;> simp_all <;> omega

/-- **Spec for `edwards.EdwardsPoint.is_torsion_free`**:
- Returns `true` if and only if the point is torsion-free (is in the prime-order subgroup)
- This is determined by checking if multiplying by the basepoint order L yields the identity element
-/
@[progress, externally_verified]
theorem is_torsion_free_spec (self : EdwardsPoint) (hself : self.IsValid) :
    is_torsion_free self ⦃ result =>
    (result ↔ L • self.toPoint = 0) ⦄ := by
  sorry
end curve25519_dalek.edwards.EdwardsPoint
