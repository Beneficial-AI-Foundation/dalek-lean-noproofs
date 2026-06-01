/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander, Liao Zhang
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromBytes
import Curve25519Dalek.Specs.Field.FieldElement51.Invert
import Curve25519Dalek.Specs.Edwards.CompressedEdwardsY.Decompress
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Add
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Sub
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Mul
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ONE
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.MINUS_ONE
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq
import Curve25519Dalek.Math.Montgomery.Representation

/-! # Spec Theorem for `MontgomeryPoint::to_edwards`

Specification and proof for `MontgomeryPoint::to_edwards`.

This function attempts to convert a MontgomeryPoint (u-coordinate only) to an
EdwardsPoint on the twisted Edwards curve, using the birational map
y = (u-1)/(u+1), followed by Edwards decompression with a specified sign bit.

**Source**: curve25519-dalek/src/montgomery.rs:224-253

-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.montgomery.MontgomeryPoint
open curve25519_dalek.backend.serial.u64.field
open curve25519_dalek.backend.serial.u64.field.FieldElement51

/-
natural language description:

    Converts a MontgomeryPoint (u-coordinate only) to an EdwardsPoint using the
    birational map y = (u-1)/(u+1) (mod p), where p = 2^255 - 19.
    Special case: when u ≡ -1 (mod p), returns None (point is on the twist).
    Otherwise, computes y, encodes it with the specified sign bit, and decompresses
    to obtain a full EdwardsPoint.

natural language specs:

    When the function returns Some(ep):
      - ep.Z is invertible in the field (invert ep.Z = ok Z_inv for some Z_inv)
      - The affine Edwards y-coordinate y = ep.Y / ep.Z satisfies the birational map:
          y * (u + 1) ≡ u - 1 (mod p)
        where u = U8x32_as_Nat mp % 2^255

    where p = 2^255 - 19
-/

@[progress]
private lemma ONE_bounds_spec : ONE ⦃ result => Field51_as_Nat result = 1 ∧ ∀ i < 5, result[i]!.val < 2 ^ 53 ⦄ := by
  unfold ONE from_limbs
  simp only [spec_ok]
  decide

@[progress]
theorem to_edwards_spec (mp : MontgomeryPoint) (sign : U8) :
      to_edwards mp sign ⦃ result =>
        (∀ ep, result = some ep →
          ∃ Z_inv,
            field.FieldElement51.invert ep.Z = ok Z_inv ∧
            let u := U8x32_as_Nat mp % 2^255
            let y := Field51_as_Nat ep.Y * Field51_as_Nat Z_inv % p
            (y * ((u + 1) % p)) % p = ((u + p - 1) % p) % p ∧ ep.IsValid )
      ⦄ := by
  sorry
end curve25519_dalek.montgomery.MontgomeryPoint
