/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.ElimMax

/-!
# From the squared bound to the distance

The localization bounds the square of the distance from the maximizer to the
shifted point; the comparison error wants the distance itself. Taking the
square root gives an order of epsilon to the three halves.

That is the honest order. Multiplied by the remaining factor of epsilon in the
comparison error it gives epsilon to the five halves, which is smaller than
epsilon squared and so does not disturb the expansion, but the intermediate
exponent is genuinely fractional and not an artefact.

## Main results

- le_sqrt_of_sq_le
- localize_dist
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## From the squared bound to the distance

`localize_maximizer` bounds the square of the distance. `cmp_err_le` wants the
distance itself. Taking the square root gives an order of epsilon to the three
halves, which is what the mathematics provides and what the expansion needs.
-/


/-- A nonnegative quantity whose square is bounded is bounded by the square
root. -/
theorem le_sqrt_of_sq_le {a B : ℝ} (ha : 0 ≤ a) (_hB : 0 ≤ B)
    (h : a ^ 2 ≤ B) : a ≤ Real.sqrt B := by
  rw [show a = Real.sqrt (a ^ 2) from (Real.sqrt_sq ha).symm]
  exact Real.sqrt_le_sqrt h

/-- **The localization distance, as a bound rather than a squared bound.** -/
theorem localize_dist {φ : EuclSpace d → ℝ} {x y : EuclSpace d}
    (hx : gradient φ x ≠ 0) {ε E : ℝ} (hε : 0 < ε)
    (hball : ‖y - x‖ ≤ ε)
    (hdom : φ (x + (y - x)) ≥ φ (x + ε • gradDir φ x))
    (hE : taylorErr φ x (y - x) - taylorErr φ x (ε • gradDir φ x) ≤ E)
    (hBnn : 0 ≤ 2 * ε * ((‖fderiv ℝ (fderiv ℝ φ) x‖ * ε ^ 2 + E)
        / ‖gradient φ x‖)) :
    ‖y - x - ε • gradDir φ x‖
      ≤ Real.sqrt (2 * ε * ((‖fderiv ℝ (fderiv ℝ φ) x‖ * ε ^ 2 + E)
          / ‖gradient φ x‖)) := by
  have hsq := localize_maximizer hx hε hball hdom hE
  exact le_sqrt_of_sq_le (norm_nonneg _) hBnn hsq

/-- The square root is nonnegative, which `cmp_err_le` requires. -/
theorem sqrt_nonneg' (B : ℝ) : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B

end

end PLaplacian
