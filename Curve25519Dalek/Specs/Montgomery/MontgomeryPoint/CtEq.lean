/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Aux
import Curve25519Dalek.Funs
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.FromBytes
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.CtEq
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ToBytes

import Mathlib.Data.Nat.ModEq
/-! # Spec Theorem for `MontgomeryPoint::ct_eq`

Specification and proof for
`curve25519_dalek::montgomery::{subtle::ConstantTimeEq for curve25519_dalek::montgomery::MontgomeryPoint}::ct_eq`.

This function compares two MontgomeryPoint values in constant time by
interpreting their 32-byte encodings as FieldElement51 values and then
delegating to FieldElement51 constant-time equality.

**Source**: curve25519-dalek/src/montgomery.rs, lines 79:4-84:5

--/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
open curve25519_dalek.backend.serial.u64.field.FieldElement51
namespace curve25519_dalek.montgomery.MontgomeryPoint.Insts.SubtleConstantTimeEq

/-
Natural language description:

    • Interprets each MontgomeryPoint byte array as a FieldElement51 using
      `FieldElement51.from_bytes`.

    • Calls the FieldElement51 constant-time equality routine on the two
      decoded field elements.

Natural language specs:

    • The function always succeeds (no panic)
    • Choice.one is returned iff the two 32-byte encodings represent the same
      field element modulo p (after the `from_bytes` reduction)
-/
/-- **Spec and proof concerning `montgomery.ConstantTimeEqMontgomeryPoint.ct_eq`**:
- No panic (always returns successfully)
- Choice.one is returned iff the u-coordinates match modulo p
- The comparison proceeds via `FieldElement51.from_bytes` and constant-time equality
-/
@[progress]
theorem ct_eq_spec (u v : MontgomeryPoint) :
    ct_eq u v ⦃ c =>
    (c = Choice.one ↔
      (U8x32_as_Nat u % 2 ^ 255) ≡ (U8x32_as_Nat v % 2 ^ 255) [MOD p]) ⦄ := by
  sorry
end curve25519_dalek.montgomery.MontgomeryPoint.Insts.SubtleConstantTimeEq
