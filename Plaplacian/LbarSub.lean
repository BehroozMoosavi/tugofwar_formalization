/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.OpContFull

@[expose] public section

/-!
# The lower relaxed limit of a difference

The dual of the upper case, by transport through negation: the lower limit is
minus the upper limit of the negation, and the negation of a difference is the
difference of the negations, so the upper result applies to the negated family
with the negated test function.

This is the fourth use of transport through negation in the development, after
the infimum results of the third layer and the lower semicontinuity of this
one. Each time it halves the work and makes the duality structural rather than
a coincidence between two separately computed results.

## Main results

- neg_sub_eq
- lbar_sub
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The lower relaxed limit of a difference

The dual of `ubar_sub`, by transport through negation:

  `lbar (u - φ) x = - ubar (-(u - φ)) x = - ubar ((-u) - (-φ)) x`,

and `ubar_sub` applies to the family `-u` with test function `-φ`.
-/


/-- The negated difference is the difference of the negations. -/
theorem neg_sub_eq (u : ℝ → EuclSpace d → ℝ) (φ : EuclSpace d → ℝ) :
    (fun ε y => -(u ε y - φ y)) = fun ε y => (-u ε y) - (-φ y) := by
  funext ε y
  ring

/-- **The lower relaxed limit of a difference.** -/
theorem lbar_sub (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {φ : EuclSpace d → ℝ}
    (hφ : Continuous φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B) (x : EuclSpace d) :
    lbar (fun ε y => u ε y - φ y) x = lbar u x - φ x := by
  rw [lbar_eq_neg_ubar_neg, lbar_eq_neg_ubar_neg]
  rw [neg_sub_eq]
  have hCn : ∀ ε y, |(-u ε y)| ≤ C := by
    intro ε y; rw [abs_neg]; exact hC ε y
  have hφn : Continuous (fun y => -φ y) := hφ.neg
  have hBn : ∀ y, |(-φ y)| ≤ B := by
    intro y; rw [abs_neg]; exact hB y
  rw [ubar_sub (fun ε y => -u ε y) hCn hφn hBn x]
  ring

end

end PLaplacian
