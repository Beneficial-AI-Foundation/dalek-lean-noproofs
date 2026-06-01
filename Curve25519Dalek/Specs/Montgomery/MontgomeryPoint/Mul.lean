/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Montgomery.Representation
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ZERO
import Curve25519Dalek.Specs.Scalar.Scalar.AsBytes
import Curve25519Dalek.ExternallyVerified
import Curve25519Dalek.Specs.Montgomery.MontgomeryPoint.AsAffine
import Curve25519Dalek.Specs.Montgomery.ProjectivePoint.DifferentialAddAndDouble

/-! # Spec Theorem for `MontgomeryPoint::mul`

Specification and proof for
`curve25519_dalek::montgomery::{core::ops::arith::Mul<&0 (curve25519_dalek::scalar::Scalar), curve25519_dalek::montgomery::MontgomeryPoint> for &1 (curve25519_dalek::montgomery::MontgomeryPoint)}::mul`.

This function performs scalar multiplication of a Montgomery point using the Montgomery ladder
algorithm. It implements constant-time scalar multiplication by processing scalar bits from
most significant to least significant.

**Source**: curve25519-dalek/src/montgomery.rs, lines 413:4-450:5

## TODO
- Complete proof
--/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open Montgomery

namespace curve25519_dalek.Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint

/-
Natural language description:

    - Interprets the MontgomeryPoint's 32-byte encoding as a field element u using
      `FieldElement51.from_bytes`.

    - Initializes two projective points:
      - x0 = (1 : 0) representing the identity (point at infinity)
      - x1 = (u : 1) representing the input point in projective coordinates

    - Processes scalar bits from most significant (bit 254) to least significant (bit 0)
      using the Montgomery ladder (Algorithm 8 from Costello-Smith 2017):
      - By scalar invariant #1, the MSB (bit 255) is always 0, so we start from bit 254
      - For each bit, conditionally swaps x0 and x1 based on bit transitions
      - Applies differential add-and-double operation
      - Maintains constant-time execution through conditional operations

    - After processing all bits, performs a final conditional swap based on the LSB

    - Converts the projective result x0 back to affine coordinates using `ProjectivePoint.as_affine`

Natural language specs:

    - The function always succeeds (no panic) given valid inputs
    - Returns a 32-byte MontgomeryPoint encoding the scalar multiplication result
    - The computation is constant-time with respect to the scalar value
    - The result represents the u-coordinate of [scalar]P on the Montgomery curve
-/


@[progress]
theorem mul_loop_spec
    (affine_u : backend.serial.u64.field.FieldElement51)
    (x0 x1 : montgomery.ProjectivePoint)
    (scalar_bytes : Array U8 32#usize)
    (prev_bit : Bool)
    (i : Isize)
    (idx0W : Field51_as_Nat x0.W = 0)
    (idx1W : Field51_as_Nat x1.W = 1)
    (idx0U : Field51_as_Nat x0.U = 1)
    :
    mul_loop affine_u x0 x1 scalar_bytes prev_bit i ⦃ res =>
    (res.2.2 =true →
      let q := (i.val / 8).toNat
      let r := (i.val % 8).toNat
      let m := ∑ i ∈ Finset.range q, 2^(8 * i) * (scalar_bytes[i]!).val
        +  2^(8 * q) * ((scalar_bytes[q]!).val % 2^(r+1))
        + 2^(8 * q+r) * prev_bit.toNat
      let u := x1.U.toField
      let u_out := res.2.1.U.toField
      let w_out := res.2.1.W.toField
      let u_ord := u_out/w_out
      res.2.1.U.IsValid ∧
      res.2.1.W.IsValid ∧
      res.1.U.IsValid ∧
      res.1.W.IsValid ∧
      w_out ≠ 0 ∧
      MontgomeryPoint.u_affine_toPoint u_ord = m • (MontgomeryPoint.u_affine_toPoint u)) ∧
    (res.2.2 = false →
      let q := (i.val / 8).toNat
      let r := (i.val % 8).toNat
      let m := ∑ i ∈ Finset.range q, 2^(8 * i) * (scalar_bytes[i]!).val
      + 2^(8 * q) * ((scalar_bytes[q]!).val % 2^(r+1))
      + 2^(8 * q+r) * prev_bit.toNat
      let u := x1.U.toField
      let u_out := res.1.U.toField
      let w_out := res.1.W.toField
      let u_ord := u_out/w_out
      res.2.1.U.IsValid ∧
      res.2.1.W.IsValid ∧
      res.1.U.IsValid ∧
      res.1.W.IsValid ∧
      w_out ≠ 0 ∧
      MontgomeryPoint.u_affine_toPoint u_ord = m • (MontgomeryPoint.u_affine_toPoint u)) ⦄
    := by
  sorry
/-- **Spec and proof concerning `montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul`**:
- No panic (always returns successfully given valid inputs)
- Implements the Montgomery ladder for constant-time scalar multiplication
- Processes scalar bits from bit 254 down to bit 0 using Algorithm 8 (Costello-Smith 2017)
- Mathematical properties of the result:
  * The result encodes the u-coordinate of the scalar multiplication [scalar]P
  * If P has u-coordinate u₀ and scalar is n (as an integer ≤ 2^255), then the result
    encodes u₀([n]P), the u-coordinate of the n-fold sum of P on the Montgomery curve
  * The Montgomery ladder maintains the invariant that x0 and x1 represent points
    differing by P throughout the computation
  * When the scalar is reduced modulo the group order L, the result corresponds to
    scalar multiplication in the prime-order subgroup
  * The result is computed via projective arithmetic and converted back to affine form
  * The returned MontgomeryPoint is a valid 32-byte encoding with value reduced modulo 2^255
  * The computation maintains constant-time guarantees: the sequence of operations
    executed is independent of the scalar bit values (only conditional swaps and
    unconditional arithmetic operations are performed)
-/
lemma aux_eq_mul (scalar : scalar.Scalar) : U8x32_as_Nat scalar.bytes =
(∑ x ∈ Finset.range ((254 :ℤ )/ 8).toNat, 2 ^ (8 * x) * (scalar.bytes[x]!).val +
        2 ^ (8 * ((254 :ℤ ) / 8).toNat) * ((scalar.bytes[((254 :ℤ )/ 8).toNat]!).val % 2 ^ (((254 :ℤ ) % 8).toNat+1) ))
        + 2^ 255 * ((scalar.bytes[31]!).val/ 2^7)
        := by
  sorry
lemma aux_lt_mul (i : ℕ) (scalar : scalar.Scalar) :
∑ x ∈ Finset.range i, 2 ^ (8 * x) * (scalar.bytes[x]!).val <  2^ (8*i)
        := by
  sorry
lemma aux_lt254_mul (scalar : scalar.Scalar) :
∑ x ∈ Finset.range ((254 :ℤ )/ 8).toNat, 2 ^ (8 * x) * (scalar.bytes[x]!).val +
        2 ^ (8 * ((254 :ℤ ) / 8).toNat) * ((scalar.bytes[((254 :ℤ ) / 8).toNat]!).val % 2 ^ (((254 :ℤ ) % 8).toNat+1) )
        <  2^ 255
        := by
  sorry
lemma aux_eq_mod_mul (scalar : scalar.Scalar) : (U8x32_as_Nat scalar.bytes) % 2^ 255 =
  (∑ x ∈ Finset.range ((254 :ℤ )/ 8).toNat, 2 ^ (8 * x) * (scalar.bytes[x]!).val +
        2 ^ (8 * ((254 :ℤ ) / 8).toNat) * ((scalar.bytes[((254 :ℤ ) / 8).toNat]!).val % 2 ^ (((254 :ℤ ) % 8).toNat+1) )):= by
  sorry
/-! ## Sub-lemmas for `mul_spec`

The following lemmas factor out the common proof patterns shared between the two
main branches (bit = true / bit = false) of the Montgomery ladder's final step.
-/

/-- **Field lifting**: When `from_bytes` produces a field element `x` satisfying
    `Field51_as_Nat x ≡ (U8x32_as_Nat P) % 2^255 [MOD p]`, we can lift this to the
    equality `x.toField = ((U8x32_as_Nat P % 2^255) : CurveField)` in `ZMod p`.

    This lemma encapsulates the common pattern of unfolding `FieldElement51.toField`
    and applying `Edwards.lift_mod_eq` with the modular congruence from `from_bytes`. -/
lemma mul_spec_toField_eq
    (x : backend.serial.u64.field.FieldElement51)
    (P : montgomery.MontgomeryPoint)
    (hmod_x : Field51_as_Nat x ≡ (U8x32_as_Nat P) % 2 ^ 255 [MOD p]) :
    x.toField = ((U8x32_as_Nat P % 2 ^ 255 : ℕ) : CurveField) := by
  sorry
/-- **MontgomeryPoint result assembly**: Given:
    - The `from_bytes` modular congruence (`hmod_x`)
    - The `as_affine` result (`res_field`) and bound (`res_bound`)
    - The Montgomery ladder loop invariant with simplified scalar (`loop_inv`)
    derives `MontgomeryPoint.mkPoint res = m • MontgomeryPoint.mkPoint P`.

    This lemma captures the common end-game of both branches: converting the
    `U8x32_as_Field` representation to a natural-number cast modulo `2^255`,
    unfolding `MontgomeryPoint.mkPoint`, and applying the field lifting to
    relate `x.toField` to the input point's u-coordinate. -/
lemma mul_spec_mkPoint_from_affine
    (res : Array U8 32#usize)
    (P : montgomery.MontgomeryPoint)
    (scalar : scalar.Scalar)
    (x : backend.serial.u64.field.FieldElement51)
    (u_div_w : CurveField)
    (hmod_x : Field51_as_Nat x ≡ (U8x32_as_Nat P) % 2 ^ 255 [MOD p])
    (res_bound : U8x32_as_Nat res < 2 ^ 255)
    (res_field : U8x32_as_Field res = u_div_w)
    (loop_inv : MontgomeryPoint.u_affine_toPoint u_div_w =
        ((U8x32_as_Nat scalar.bytes) % 2 ^ 255) • MontgomeryPoint.u_affine_toPoint x.toField) :
    MontgomeryPoint.mkPoint res =
        ((U8x32_as_Nat scalar.bytes) % 2 ^ 255) • MontgomeryPoint.mkPoint P := by
  sorry
/- **Spec and proof concerning `montgomery.MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul`**:
- No panic (always returns successfully given valid inputs)
- Implements the Montgomery ladder for constant-time scalar multiplication
- Processes scalar bits from bit 254 down to bit 0 using Algorithm 8 (Costello-Smith 2017)
- Mathematical properties of the result:
  * The result encodes the u-coordinate of the scalar multiplication [scalar]P
  * If P has u-coordinate u₀ and scalar is n (as an integer ≤ 2^255), then the result
    encodes u₀([n]P), the u-coordinate of the n-fold sum of P on the Montgomery curve
  * The Montgomery ladder maintains the invariant that x0 and x1 represent points
    differing by P throughout the computation
  * When the scalar is reduced modulo the group order L, the result corresponds to
    scalar multiplication in the prime-order subgroup
  * The result is computed via projective arithmetic and converted back to affine form
  * The returned MontgomeryPoint is a valid 32-byte encoding with value reduced modulo 2^255
  * The computation maintains constant-time guarantees: the sequence of operations
    executed is independent of the scalar bit values (only conditional swaps and
    unconditional arithmetic operations are performed)
-/

@[progress, externally_verified]
theorem mul_spec (P : montgomery.MontgomeryPoint) (scalar : scalar.Scalar) :
    mul P scalar ⦃ res =>
      let m:= (U8x32_as_Nat scalar.bytes) % 2^255
      MontgomeryPoint.mkPoint res = m • (MontgomeryPoint.mkPoint P) ⦄ := by
  sorry
end curve25519_dalek.Shared1MontgomeryPoint.Insts.CoreOpsArithMulShared0ScalarMontgomeryPoint

namespace curve25519_dalek.Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint

/- [curve25519_dalek::montgomery::{core::ops::arith::Mul<&0 (curve25519_dalek::montgomery::MontgomeryPoint), curve25519_dalek::montgomery::MontgomeryPoint> for &1 (curve25519_dalek::scalar::Scalar)}::mul]:
   Source: 'curve25519-dalek/src/montgomery.rs', lines 462:4-464:5
-/

/-
Natural language description:

    - This is the commutative variant of scalar multiplication: Scalar * MontgomeryPoint.

    - Simply delegates to the MontgomeryPoint * Scalar implementation by swapping arguments.

Natural language specs:

    - The function always succeeds (no panic) given valid inputs
    - Returns the same result as the reverse multiplication (point * scalar)
    - Inherits all mathematical properties from MontgomeryPoint::mul
-/
/-- **Spec and proof concerning `montgomery.MulShared1ScalarShared0MontgomeryPointMontgomeryPoint.mul`**:
- No panic (always returns successfully given valid inputs)
- Implements scalar multiplication via delegation to the reverse operation
- The result is mathematically equivalent to [scalar]point
- Mathematical properties of the result:
  * The result encodes the u-coordinate of the scalar multiplication [scalar]point
  * Mathematically equivalent to MontgomeryPoint::mul with swapped arguments
  * If point has u-coordinate u₀ and scalar is n (as an integer ≤ 2^255), then the result
    encodes u₀([n]point), the u-coordinate of the n-fold sum of point on the Montgomery curve
  * The computation maintains constant-time guarantees inherited from the underlying
    Montgomery ladder implementation
  * The returned MontgomeryPoint is a valid 32-byte encoding with value reduced modulo 2^255
-/
@[progress]
theorem mul_spec (scalar : scalar.Scalar) (P : montgomery.MontgomeryPoint) :
    mul scalar P ⦃ res =>
    let m:= (U8x32_as_Nat scalar.bytes) % 2^255
    MontgomeryPoint.mkPoint res = m • (MontgomeryPoint.mkPoint P) ⦄
    := by
  sorry
end curve25519_dalek.Shared1Scalar.Insts.CoreOpsArithMulShared0MontgomeryPointMontgomeryPoint

namespace curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulSharedBScalarMontgomeryPoint

/- [curve25519_dalek::montgomery::{core::ops::arith::Mul<&'b (curve25519_dalek::scalar::Scalar), curve25519_dalek::montgomery::MontgomeryPoint> for curve25519_dalek::montgomery::MontgomeryPoint}::mul]:
   Source: 'curve25519-dalek/src/macros.rs', lines 93:12-95:13
-/

/-
Natural language description:

    - This is another variant of scalar multiplication: MontgomeryPoint * &'b Scalar.

    - Delegates to the core MontgomeryPoint * Scalar implementation.

Natural language specs:

    - The function always succeeds (no panic) given valid inputs
    - Returns the same result as the underlying scalar multiplication
    - Inherits all mathematical properties from MontgomeryPoint::mul
-/
/-- **Spec and proof concerning `montgomery.MulMontgomeryPointSharedBScalarMontgomeryPoint.mul`**:
- No panic (always returns successfully given valid inputs)
- Implements scalar multiplication via delegation to the underlying operation
- The result is mathematically equivalent to [scalar]point
- Mathematical properties of the result:
  * The result encodes the u-coordinate of the scalar multiplication [scalar]point
  * Mathematically equivalent to MulShared1MontgomeryPointShared0ScalarMontgomeryPoint.mul
  * If point has u-coordinate u₀ and scalar is n (as an integer ≤ 2^255), then the result
    encodes u₀([n]point), the u-coordinate of the n-fold sum of point on the Montgomery curve
  * The Montgomery ladder maintains the invariant that x0 and x1 represent points
    differing by point throughout the computation
  * The computation maintains constant-time guarantees inherited from the underlying
    Montgomery ladder implementation
  * The returned MontgomeryPoint is a valid 32-byte encoding with value reduced modulo 2^255
-/
@[progress]
theorem mul_spec (P : MontgomeryPoint) (rhs : scalar.Scalar) :
    mul P rhs ⦃ res =>
    let m:= (U8x32_as_Nat rhs.bytes) % 2^255
    MontgomeryPoint.mkPoint res = m • (MontgomeryPoint.mkPoint P) ⦄
 := by
  sorry
end curve25519_dalek.montgomery.MontgomeryPoint.Insts.CoreOpsArithMulSharedBScalarMontgomeryPoint

namespace curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint

/-
Natural language description:

    - This is the non-borrow variant of scalar multiplication: Scalar * MontgomeryPoint.

    - Delegates to the shared reference implementation
      MulShared1ScalarShared0MontgomeryPointMontgomeryPoint.mul.

Natural language specs:

    - The function always succeeds (no panic) given valid inputs
    - Returns the same result as the underlying scalar multiplication
    - Inherits all mathematical properties from the core Montgomery ladder implementation
-/
/-- **Spec and proof concerning `montgomery.MulScalarMontgomeryPointMontgomeryPoint.mul`**:
- No panic (always returns successfully given valid inputs)
- Implements scalar multiplication via delegation to the underlying operation
- The result is mathematically equivalent to [scalar]point
- Mathematical properties of the result:
  * The result encodes the u-coordinate of the scalar multiplication [scalar]point
  * Mathematically equivalent to MulShared1ScalarShared0MontgomeryPointMontgomeryPoint.mul
  * If point has u-coordinate u₀ and scalar is n (as an integer ≤ 2^255), then the result
    encodes u₀([n]point), the u-coordinate of the n-fold sum of point on the Montgomery curve
  * The Montgomery ladder maintains the invariant that x0 and x1 represent points
    differing by point throughout the computation
  * The computation maintains constant-time guarantees inherited from the underlying
    Montgomery ladder implementation
  * The returned MontgomeryPoint is a valid 32-byte encoding with value reduced modulo 2^255
-/
@[progress]
theorem mul_spec (scalar : Scalar) (P : montgomery.MontgomeryPoint) :
    mul scalar P ⦃ res =>
    let m:= (U8x32_as_Nat scalar.bytes) % 2^255
    MontgomeryPoint.mkPoint res = m • (MontgomeryPoint.mkPoint P) ⦄
 := by
  sorry
end curve25519_dalek.scalar.Scalar.Insts.CoreOpsArithMulMontgomeryPointMontgomeryPoint
