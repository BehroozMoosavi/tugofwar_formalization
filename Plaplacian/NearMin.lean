/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.LbarSub

/-!
# Frequent near-minimum

The dual of frequent near-contact. At a minimum of the lower relaxed limit
minus the test function, the family minus the test function is frequently
within any given distance above that minimum.

The proof is three lines, because the duals it needs were built by transport
rather than by parallel argument: the lower limit of a difference, and the
frequent approach from above. That is the dividend from transporting instead
of reproving, and it is why the supersolution half of this layer is largely
assembly rather than fresh work.

## Main results

- frequently_near_min
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # Frequent near-minimum

The dual of `frequently_near_max`. At a minimum of the lower relaxed limit
minus the test function, the family minus the test function is frequently
within any given distance of that minimum --- from above this time.

By transport: the statement for the lower limit of `u` is the statement for
the upper limit of `-u` with test function `-φ`, negated.
-/


/-- **Frequent near-minimum.** -/
theorem frequently_near_min (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {φ : EuclSpace d → ℝ}
    (hφ : Continuous φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B)
    (x : EuclSpace d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ᶠ q in relaxFilter x,
      u q.1 q.2 - φ q.2 < lbar u x - φ x + δ := by
  -- the bound in terms of the difference's lower limit
  have hbd := abs_sub_le_of_bounds u hC hB
  have heq := lbar_sub u hC hφ hB x
  have hlt : lbar (fun ε y => u ε y - φ y) x
      < lbar u x - φ x + δ := by
    rw [heq]; linarith [hδ]
  exact frequently_gt_of_lbar_lt (fun ε y => u ε y - φ y) hbd x hlt

end

end PLaplacian
