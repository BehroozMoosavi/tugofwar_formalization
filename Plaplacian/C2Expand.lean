/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.C2Taylor

@[expose] public section

/-!
# The C two bound in expansion form

The self-contained C two estimate, and its identification with the error the
average expansion already carries. The two definitions of the second-order
error, one made for the expansion and one for this argument, turn out to be
the same expression, so the estimate applies to the existing expansion with no
restatement.

The C three results are left in place. They are correct and their rate is
sharper: the third-derivative bound gives order three in the increment, where
the C two argument gives only little-o of order two. The library carries both,
and which to use depends on whether generality or the rate is wanted.

## Main results

- exists_err2_le
- taylorErr_eq_err2
- exists_taylorErr_le
-/

open Set Topology Filter MeasureTheory Metric Asymptotics

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The C² bound in expansion form

`err2_le` carries the derivative bound as a hypothesis. Combining it with
`fderiv_increment_small`, which supplies that bound, gives the self-contained
statement: for every prescribed multiple there is a radius within which the
second-order Taylor error is below that multiple of the squared increment.

The `C³` results are left in place. They are correct and their error rate is
sharper: the third-derivative bound gives order three in the increment, where
the `C²` argument gives only little-o of order two. The library carries both,
and which to use depends on whether generality or the rate is wanted.
-/


/-- **The `C²` second-order Taylor estimate.** -/
theorem exists_err2_le {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x : EuclSpace d) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ w : EuclSpace d, ‖w‖ < δ →
      |err2 φ x w| ≤ η * ‖w‖ ^ 2 := by
  obtain ⟨δ, hδ, hbd⟩ := fderiv_increment_small hφ x hη
  exact ⟨δ, hδ, fun w hw => err2_le hφ x hη hbd hw⟩

/-- The error of `Plaplacian.AvgExpansion` and the error here agree. -/
theorem taylorErr_eq_err2 (φ : EuclSpace d → ℝ) (x w : EuclSpace d) :
    taylorErr φ x w = err2 φ x w := by
  unfold taylorErr err2
  ring

/-- **The `C²` estimate for the expansion's error.** -/
theorem exists_taylorErr_le {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x : EuclSpace d) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ w : EuclSpace d, ‖w‖ < δ →
      |taylorErr φ x w| ≤ η * ‖w‖ ^ 2 := by
  obtain ⟨δ, hδ, hbd⟩ := exists_err2_le hφ x hη
  refine ⟨δ, hδ, fun w hw => ?_⟩
  rw [taylorErr_eq_err2]
  exact hbd w hw

end

end PLaplacian
