/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Curve25519Dalek.Funs
import Curve25519Dalek.Specs.Backend.Serial.U64.Field.FieldElement51.ConditionalSelect

/-! # Spec Theorem for `AffinePoint::conditional_select`

Specification and proof for the `ConditionallySelectable` trait implementation for `AffinePoint`.

This function conditionally selects between two affine Edwards points based on a `Choice` value
by applying `FieldElement51::conditional_select` component-wise to the coordinates (x, y).

Returns `b` when `choice = 1` and `a` when `choice = 0`, in constant time.

**Source**: curve25519-dalek/src/edwards/affine.rs
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP
namespace curve25519_dalek.edwards.affine.AffinePoint.Insts.SubtleConditionallySelectable

/-
natural language description:

- Takes two AffinePoints `a` and `b` and a `Choice` value
- Returns one of the two points based on the choice, in constant time
- Implementation: applies `FieldElement51::conditional_select` component-wise
  to the coordinates (x, y)

natural language specs:

- The function always succeeds (no panic)
- Returns `b` when `choice = 1` and `a` when `choice = 0`
-/

/--
**Spec and proof concerning `edwards.affine.AffinePoint.Insts.SubtleConditionallySelectable.conditional_select`**:
- No panic (always returns successfully)
- Returns `b` when `choice = 1` and `a` when `choice = 0`
-/
@[progress]
theorem conditional_select_spec
    (a b : edwards.affine.AffinePoint)
    (choice : subtle.Choice) :
    conditional_select a b choice ⦃ (result : edwards.affine.AffinePoint) =>
      result = if choice.val = 1#u8 then b else a ⦄ := by
  sorry
end curve25519_dalek.edwards.affine.AffinePoint.Insts.SubtleConditionallySelectable
