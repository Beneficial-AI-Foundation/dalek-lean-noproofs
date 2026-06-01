/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Dablander
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Math.Ristretto.Representation
import Curve25519Dalek.Specs.Ristretto.CompressedRistretto.Step1
import Curve25519Dalek.Specs.Ristretto.CompressedRistretto.Step2

/-! # Spec Theorem for `CompressedRistretto::decompress`

Specification and proof for `CompressedRistretto::decompress`.

This function implements the Ristretto decompression (DECODE) function, which attempts to
decode a (valid) 32-byte representation back to a RistrettoPoint. The function is defined in the

- [Ristretto specification](https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-ristretto255-decaf448-08#section-4.3.1).

It takes a CompressedRistretto (a 32-byte array) and attempts to produce the associated RistrettoPoint,
returning None if the input byte array is not a valid canonical encoding.

**Source**: curve25519-dalek/src/ristretto.rs
-/

open Aeneas Aeneas.Std Result Edwards Aeneas.Std.WP
open curve25519_dalek.ristretto
namespace curve25519_dalek.ristretto.CompressedRistretto

/-- When `decompress_step1` returns `some val`, `val` equals the field element `s.toField`
    computed by step_1. This follows from the uniqueness of the output value. -/
private lemma decompress_step1_val_eq (c : CompressedRistretto)
    (s : backend.serial.u64.field.FieldElement51)
    (hs : s.toField = ((U8x32_as_Nat c % 2 ^ 255 : ℕ) : ZMod p))
    {val : ZMod p} (h : decompress_step1 c = some val) :
    val = s.toField := by
  simp only [decompress_step1] at h
  split_ifs at h with h_cond
  simp only [Bool.or_eq_true, decide_eq_true_eq, ge_iff_le, not_or, not_le] at h_cond
  have h_lt_p : U8x32_as_Nat c < p := h_cond.1
  have h_lt_255 : U8x32_as_Nat c < 2 ^ 255 := lt_trans h_lt_p (by decide)
  rw [Option.some.injEq] at h
  rw [← h, hs, Nat.mod_eq_of_lt h_lt_255]

/-- **Spec and proof concerning `ristretto.CompressedRistretto.decompress`**:
- The function always succeeds for all U8x32 input arrays (no panic)
- If the input is not valid, then the output is none
- If the input is valid, then the output is a valid Ristretto point that reflects the
  output of the pure mathematical decompression function
-/
@[progress]
theorem decompress_spec (comp : CompressedRistretto) :
    decompress comp ⦃ result =>
    (¬comp.IsValid → result = none) ∧
    (comp.IsValid →
        ∃ rist,
        result = some rist ∧
        RistrettoPoint.IsValid rist ∧
        decompress_pure comp = some rist.toPoint) ⦄ := by
  sorry
end curve25519_dalek.ristretto.CompressedRistretto
