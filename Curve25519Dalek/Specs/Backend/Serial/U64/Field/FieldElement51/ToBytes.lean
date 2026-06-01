/-
Copyright (c) 2025 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.Reduce
import Curve25519Dalek.Tactics
import Curve25519Dalek.ExternallyVerified


/-! # to_bytes

Specification and proof for `FieldElement51::to_bytes`.

Much of the proof and aux lemmas contributed by Son Ho.

This function converts a field element to its canonical 32-byte little-endian representation.
It performs reduction modulo 2^255-19 and encodes the result as bytes.

Source: curve25519-dalek/src/backend/serial/u64/field.rs

## TODO
- Complete proof
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace curve25519_dalek.backend.serial.u64.field.FieldElement51

-- TODO: generalize and add to the standard library
@[local simp]
theorem U64_cast_U8 (x : U64) : (UScalar.cast UScalarTy.U8 x).val = x.val % 2^8 := by
  sorry
theorem recompose_decomposed_limb (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val =
  limb.val % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 8 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 16 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 24 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 32 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 40 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 48 % 2 ^ 8)
  := by
  sorry
theorem recompose_decomposed_limb_shift3 (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val <<< 3 % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 5 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 13 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 21 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 29 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 37 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 45 % 2 ^ 8) =
  2 ^ 3 * limb.val := by
  sorry
theorem recompose_decomposed_limb_shift6 (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val <<< 6 % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 2 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 10 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 18 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 26 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 34 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 42 % 2 ^ 8)
  + 2 ^ 56 * (limb.val >>> 50 % 2 ^ 8) =
  2 ^ 6 * limb.val := by
  sorry
theorem recompose_decomposed_limb_shift1 (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val <<< 1 % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 7 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 15 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 23 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 31 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 39 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 47 % 2 ^ 8) =
  2 ^ 1 * limb.val := by
  sorry
theorem recompose_decomposed_limb_shift4 (limb : U64) (h : limb.val < 2 ^ 51) :
  limb.val <<< 4 % 2 ^ 8
  + 2 ^ 8 * (limb.val >>> 4 % 2 ^ 8)
  + 2 ^ 16 * (limb.val >>> 12 % 2 ^ 8)
  + 2 ^ 24 * (limb.val >>> 20 % 2 ^ 8)
  + 2 ^ 32 * (limb.val >>> 28 % 2 ^ 8)
  + 2 ^ 40 * (limb.val >>> 36 % 2 ^ 8)
  + 2 ^ 48 * (limb.val >>> 44 % 2 ^ 8) =
  2 ^ 4 * limb.val := by
  sorry
theorem decompose_or_limbs_shift3 (limb0 limb1 : U64) (h : limb0.val < 2 ^ 51) :
  ((limb0.val >>> 48 ||| limb1.val <<< 3 % U64.size) % 2 ^ 8) =
  (limb0.val >>> 48 % 2 ^ 8) + ((limb1.val <<< 3) % 2 ^ 8) := by
  sorry
theorem decompose_or_limbs_shift6 (limb0 limb1 : U64) (h : limb0.val < 2 ^ 51) :
  ((limb0.val >>> 45 ||| limb1.val <<< 6 % U64.size) % 2 ^ 8) =
  (limb0.val >>> 45 % 2 ^ 8) + ((limb1.val <<< 6) % 2 ^ 8) := by
  sorry
theorem decompose_or_limbs_shift1 (limb0 limb1 : U64) (h : limb0.val < 2 ^ 51) :
  ((limb0.val >>> 50 ||| limb1.val <<< 1 % U64.size) % 2 ^ 8) =
  (limb0.val >>> 50 % 2 ^ 8) + ((limb1.val <<< 1) % 2 ^ 8) := by
  sorry
theorem decompose_or_limbs_shift4 (limb0 limb1 : U64) (h : limb0.val < 2 ^ 51) :
  ((limb0.val >>> 47 ||| limb1.val <<< 4 % U64.size) % 2 ^ 8) =
  (limb0.val >>> 47 % 2 ^ 8) + ((limb1.val <<< 4) % 2 ^ 8) := by
  sorry
/-- Byte-by-byte packing formula for 5 × 51-bit limbs into 32 LE bytes.
    Matches the Rust source (field.rs:419-452) and the Lean extraction.
    The 4 boundary bytes (6, 12, 19, 25) combine bits from adjacent limbs.

    NOTE: This describes the byte packing of CANONICALIZED limbs (each < 2^51).
    The full `to_bytes` function first reduces and canonicalizes before packing. -/
def bytes_match_limbs (L : Array U64 5#usize) (s : Array U8 32#usize) : Prop :=
  -- Limb 0 (bits 0-50) → bytes 0-6
  s.val[0]!.val = L.val[0]!.val % 2^8 ∧
  s.val[1]!.val = L.val[0]!.val >>> 8 % 2^8 ∧
  s.val[2]!.val = L.val[0]!.val >>> 16 % 2^8 ∧
  s.val[3]!.val = L.val[0]!.val >>> 24 % 2^8 ∧
  s.val[4]!.val = L.val[0]!.val >>> 32 % 2^8 ∧
  s.val[5]!.val = L.val[0]!.val >>> 40 % 2^8 ∧
  s.val[6]!.val = (L.val[0]!.val >>> 48 ||| L.val[1]!.val <<< 3 % U64.size) % 2^8 ∧
  -- Limb 1 (bits 51-101) → bytes 7-12
  s.val[7]!.val = L.val[1]!.val >>> 5 % 2^8 ∧
  s.val[8]!.val = L.val[1]!.val >>> 13 % 2^8 ∧
  s.val[9]!.val = L.val[1]!.val >>> 21 % 2^8 ∧
  s.val[10]!.val = L.val[1]!.val >>> 29 % 2^8 ∧
  s.val[11]!.val = L.val[1]!.val >>> 37 % 2^8 ∧
  s.val[12]!.val = (L.val[1]!.val >>> 45 ||| L.val[2]!.val <<< 6 % U64.size) % 2^8 ∧
  -- Limb 2 (bits 102-152) → bytes 13-19
  s.val[13]!.val = L.val[2]!.val >>> 2 % 2^8 ∧
  s.val[14]!.val = L.val[2]!.val >>> 10 % 2^8 ∧
  s.val[15]!.val = L.val[2]!.val >>> 18 % 2^8 ∧
  s.val[16]!.val = L.val[2]!.val >>> 26 % 2^8 ∧
  s.val[17]!.val = L.val[2]!.val >>> 34 % 2^8 ∧
  s.val[18]!.val = L.val[2]!.val >>> 42 % 2^8 ∧
  s.val[19]!.val = (L.val[2]!.val >>> 50 ||| L.val[3]!.val <<< 1 % U64.size) % 2^8 ∧
  -- Limb 3 (bits 153-203) → bytes 20-25
  s.val[20]!.val = L.val[3]!.val >>> 7 % 2^8 ∧
  s.val[21]!.val = L.val[3]!.val >>> 15 % 2^8 ∧
  s.val[22]!.val = L.val[3]!.val >>> 23 % 2^8 ∧
  s.val[23]!.val = L.val[3]!.val >>> 31 % 2^8 ∧
  s.val[24]!.val = L.val[3]!.val >>> 39 % 2^8 ∧
  s.val[25]!.val = (L.val[3]!.val >>> 47 ||| L.val[4]!.val <<< 4 % U64.size) % 2^8 ∧
  -- Limb 4 (bits 204-254) → bytes 26-31
  s.val[26]!.val = L.val[4]!.val >>> 4 % 2^8 ∧
  s.val[27]!.val = L.val[4]!.val >>> 12 % 2^8 ∧
  s.val[28]!.val = L.val[4]!.val >>> 20 % 2^8 ∧
  s.val[29]!.val = L.val[4]!.val >>> 28 % 2^8 ∧
  s.val[30]!.val = L.val[4]!.val >>> 36 % 2^8 ∧
  s.val[31]!.val = L.val[4]!.val >>> 44 % 2^8


/-- Byte packing correctness: when all limbs < 2^51 and bytes match the packing formula,
    the little-endian byte interpretation equals the radix-2^51 limb interpretation. -/
theorem byte_packing_eq (L : Array U64 5#usize) (s : Array U8 32#usize)
    (hL : ∀ i < 5, (L.val[i]! : U64).val < 2 ^ 51)
    (hbytes : bytes_match_limbs L s) :
    U8x32_as_Nat s = Field51_as_Nat L := by
  sorry
/-- AND with a mask whose value is 2^51-1 gives a value < 2^51. -/
private lemma and_mask_lt_pow (x mask : U64) (hm : mask.val = 2 ^ 51 - 1) :
    (x &&& mask).val < 2^51 := by
  rw [UScalar.val_and, hm]
  have := @Nat.and_le_right x.val (2^51 - 1)
  omega

/-- For a U8 value < 128, AND with 128 is 0 (bit 7 is clear). -/
private lemma u8_and_128_eq_zero_of_lt (x : U8) (h : x.val < 128) :
    (x &&& 128#u8).val = 0 := by
  bvify 8 at *
  bv_decide

/-- A 64-bit value AND'd with 2^51-1, then shifted right by 44, fits in 7 bits. -/
private lemma masked_shift44_lt_128 (x : BitVec 64) :
    ((x &&& (BitVec.ofNat 64 (2^51 - 1))) >>> 44).toNat < 128 := by
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_and, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  have := @Nat.and_le_right x.toNat (2^51 - 1)
  norm_num at *; omega

/-! ## Spec for `to_bytes` -/

set_option maxHeartbeats 600000 in -- heavy progress*
/-- **Spec for `backend.serial.u64.field.FieldElement51.to_bytes`**:

This function converts a field element to its canonical 32-byte little-endian representation.
The implementation performs reduction modulo p = 2^255-19 to ensure the result is in
canonical form.

The algorithm:
1. Reduces the field element using `reduce` to ensure all limbs are within bounds
2. Performs a final conditional reduction to ensure the result is < p
3. Packs the 5 limbs (each 51 bits) into 32 bytes in little-endian format

Specification:
- The function succeeds (no panic)
- The natural number interpretation of the byte array is congruent to the field element value modulo p
- The byte array represents the unique canonical form (0 ≤ value < p)
-/
@[externally_verified, progress] -- proven in Verus
theorem to_bytes_spec (self : backend.serial.u64.field.FieldElement51) :
    to_bytes self ⦃ result =>
    U8x32_as_Nat result ≡ Field51_as_Nat self [MOD p] ∧
    U8x32_as_Nat result < p ⦄ := by
  sorry
end curve25519_dalek.backend.serial.u64.field.FieldElement51
