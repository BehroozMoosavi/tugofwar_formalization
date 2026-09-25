/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.WeightErr

/-!
# The expansion with a bounded error

The expansion restated with the two error halves supplied together with
bounds. The conclusion bounds the total error by the sum of those bounds,
since for p at least two the weights do not amplify.

The bounds enter as hypotheses rather than being derived afterwards, and that
is the substance. Deriving a bound from the error itself, dividing by epsilon
squared and multiplying back, is true of any quantity and carries no
information. Here the bounds are inputs and the theorem transports them, so
instantiating with the cubic average bound and the localization bound gives a
total error with a constant independent of epsilon.

## Main results

- tugOfWarOp_expansion_bounded
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The expansion with a bound independent of epsilon

The expansion is restated with the two error halves supplied as hypotheses
carrying their own bounds. The conclusion then bounds the total error by the
sum of those bounds, via `weighted_error_le`.

The constants are the halves' own. They do not depend on `ε` --- that is the
whole point, and it is why the hypotheses are stated with the bounds attached
rather than the bound being derived afterwards from the error itself.
-/

/-- **The expansion with a bounded error.**

Given the two halves with their errors bounded by `B₁` and `B₂`, the operator
expands with total error at most `B₁ + B₂`. -/
theorem tugOfWarOp_expansion_bounded (p : ℝ) (hp : 2 ≤ p)
    (hpd : 0 < p + (d : ℝ)) (ε : ℝ) (φ : EuclSpace d → ℝ)
    (x : EuclSpace d) {e₁ e₂ B₁ B₂ : ℝ}
    (hS : (sSup (φ '' ball x ε) + sInf (φ '' ball x ε)) / 2
        = φ x + (ε ^ 2 / 2)
            * infLaplacianOf (gradient φ x) (fderiv ℝ (fderiv ℝ φ) x) + e₁)
    (hA : (⨍ y in ball x ε, φ y)
        = φ x + ε ^ 2 / (2 * ((d : ℝ) + 2))
            * laplacianOf (fderiv ℝ (fderiv ℝ φ) x) + e₂)
    (hB₁ : |e₁| ≤ B₁) (hB₂ : |e₂| ≤ B₂) :
    ∃ E : ℝ,
      tugOfWarOp p ε φ x
          = φ x + ε ^ 2 / (2 * (p + (d : ℝ)))
              * normPLapOf p (gradient φ x) (fderiv ℝ (fderiv ℝ φ) x) + E
        ∧ |E| ≤ B₁ + B₂ := by
  refine ⟨(p - 2) / (p + (d : ℝ)) * e₁
    + ((d : ℝ) + 2) / (p + (d : ℝ)) * e₂, ?_, ?_⟩
  · exact tugOfWarOp_expansion_normPLap p hpd ε φ x hS hA
  · calc |(p - 2) / (p + (d : ℝ)) * e₁
            + ((d : ℝ) + 2) / (p + (d : ℝ)) * e₂|
        ≤ |e₁| + |e₂| := weighted_error_le p hp hpd e₁ e₂
      _ ≤ B₁ + B₂ := by linarith [hB₁, hB₂]

end

end PLaplacian
