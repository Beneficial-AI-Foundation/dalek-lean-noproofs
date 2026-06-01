/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Liao Zhang
-/
import Aeneas
import Curve25519Dalek.Funs
import Curve25519Dalek.Aux
import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.M


set_option exponentiation.threshold 416

/-! # MulInternal

The main statement concerning `mul_internal` is `mul_internal_spec` (below).
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

attribute [-simp] Int.reducePow Nat.reducePow

/-! ## Spec for `mul_internal` -/

set_option maxHeartbeats 400000 in -- heavy simp
/-- **Spec for `backend.serial.u64.scalar.Scalar52.mul_internal`**:
- The result represents the product of the two input field elements
- Requires that each input limb is at most 62 bits to prevent overflow -/
@[progress]
theorem mul_internal_spec (a b : Array U64 5#usize)
    (ha : ∀ i < 5, a[i]!.val < 2 ^ 62) (hb : ∀ i < 5, b[i]!.val < 2 ^ 62) :
    mul_internal a b ⦃ (result : Array U128 9#usize) =>
      Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat b ∧
      (∀ i < 9, result[i]!.val < 2 ^ 127) ⦄ := by
  sorry
end curve25519_dalek.backend.serial.u64.scalar.Scalar52
