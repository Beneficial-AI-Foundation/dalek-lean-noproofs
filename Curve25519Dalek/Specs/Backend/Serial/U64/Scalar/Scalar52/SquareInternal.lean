import Curve25519Dalek.Math.Basic
import Curve25519Dalek.Aux
import Curve25519Dalek.Tactics
import Curve25519Dalek.Specs.Backend.Serial.U64.Scalar.M


set_option exponentiation.threshold 416


/-! # SquareInternal

The main statement concerning `square_internal` is `square_internal_spec` (below).
-/

open Aeneas Aeneas.Std Result Aeneas.Std.WP

namespace curve25519_dalek.backend.serial.u64.scalar.Scalar52

attribute [-simp] Int.reducePow Nat.reducePow

/-- Helper: x * y < 2^124 -/
private theorem bounds_mul {x y : Nat} (hx : x < 2 ^ 62) (hy : y < 2 ^ 62) :
    x * y < 2^124 := by
  nlinarith [hx, hy]

/-- Helper: x * x < 2^124 (Special case for squares) -/
private theorem bounds_sq {x : Nat} (hx : x < 2 ^ 62) : x * x < 2^124 := bounds_mul hx hx

/-- Helper: 2 * x * y < 2^125 -/
private theorem bounds_mul2 {x y : Nat} (hx : x < 2 ^ 62) (hy : y < 2 ^ 62) :
    2 * x * y < 2^125 := by
  nlinarith [hx, hy]

/-- Helper: a + b < 2^127 -/
private theorem bounds_add {a b : Nat} (ha : a < 2 ^ 126) (hb : b < 2 ^ 126) :
    a + b < 2^127 := by
  nlinarith [ha,hb]


/-! ## Spec for `square_internal` -/

/-
Square_internal computes `a^2` using 52-bit limb optimizations.

Corresponds to the Rust function `Scalar52::square_internal` defined
in `curve25519-dalek/src/backend/serial/u64/scalar.rs`.
-/

/-- **Spec for `square_internal`**:
- Does not error and hence returns a result
- The result represents the square of the input field element
- Requires each limb to be less than 62 bits to prevent overflow
(The optimal bound on the limbs is 2^64 / √5  ≈ 2^62.839) -/
@[progress]
theorem square_internal_spec (a : Array U64 5#usize) (ha : ∀ i, i < 5 → (a[i]!).val < 2 ^ 62) :
    square_internal a ⦃ result =>
    Scalar52_wide_as_Nat result = Scalar52_as_Nat a * Scalar52_as_Nat a ∧
    (∀ i < 9, result[i]!.val < 2 ^ 127) ⦄ := by
  sorry
end curve25519_dalek.backend.serial.u64.scalar.Scalar52
