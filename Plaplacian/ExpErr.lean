/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.ExtAvgErr

/-!
# The expansion error, from both halves

The expansion of the step operator, with its error bounded by the sum of the
bounds on its two halves. Each half error is defined as the difference from
its expansion, so the expansion equations hold by computation and by the
average expansion, and the weighting lemma of the third layer combines them,
the weights not amplifying.

The extreme-value half was bounded over the closed ball; the operator takes
its extreme values over the open one. The two agree for a continuous
function, which is where the open-ball choice forced by measurability is paid
for once more.

The halves enter as hypotheses carrying their bounds. Supplying those bounds
uniformly in the base point is what the preceding files did; here they are
combined.

## Main results

- expansion_err_le
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The expansion error, from both uniform halves

`tugOfWarOp_expansion_bounded` of the third layer takes the extreme-value and
average errors with bounds and returns the total, the weights not amplifying.
Feeding it the two uniform halves gives the expansion error bounded by their
sum.

The extreme-value half was proved over the closed ball, and the operator takes
its extreme values over the open one; the two agree for a continuous
function, which is where the open-ball choice forced by measurability is paid
for once more.

The two halves enter as hypotheses carrying their bounds, so that this step is
the weighting and the conversion of balls, and nothing else.
-/


/-- **The expansion error, bounded by the sum of the two halves.** -/
theorem expansion_err_le [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ) {x : EuclSpace d}
    {ε B₁ B₂ : ℝ} (hε : 0 < ε)
    (hext : |(sSup (φ '' closedBall x ε) + sInf (φ '' closedBall x ε)) / 2
        - (φ x + ε ^ 2 / 2 * infLaplacianOf (gradient φ x)
            (fderiv ℝ (fderiv ℝ φ) x))| ≤ B₁)
    (havg : |⨍ z in ball (0 : EuclSpace d) ε, taylorErr φ x z| ≤ B₂) :
    ∃ E : ℝ,
      tugOfWarOp p ε φ x
          = φ x + ε ^ 2 / (2 * (p + (d : ℝ)))
              * normPLapOf p (gradient φ x) (fderiv ℝ (fderiv ℝ φ) x) + E
        ∧ |E| ≤ B₁ + B₂ := by
  have hcont : Continuous φ := hφ.continuous
  -- the extreme-value half, over the open ball
  set e₁ := (sSup (φ '' ball x ε) + sInf (φ '' ball x ε)) / 2
    - (φ x + ε ^ 2 / 2 * infLaplacianOf (gradient φ x)
        (fderiv ℝ (fderiv ℝ φ) x)) with he₁
  have hS : (sSup (φ '' ball x ε) + sInf (φ '' ball x ε)) / 2
      = φ x + ε ^ 2 / 2 * infLaplacianOf (gradient φ x)
          (fderiv ℝ (fderiv ℝ φ) x) + e₁ := by
    rw [he₁]; ring
  have hB₁ : |e₁| ≤ B₁ := by
    rw [he₁, sSup_ball_eq_closedBall hcont x hε,
      sInf_ball_eq_closedBall hcont x hε]
    exact hext
  -- the average half
  set e₂ := ⨍ z in ball (0 : EuclSpace d) ε, taylorErr φ x z with he₂
  have hA : (⨍ y in ball x ε, φ y)
      = φ x + ε ^ 2 / (2 * ((d : ℝ) + 2))
          * laplacianOf (fderiv ℝ (fderiv ℝ φ) x) + e₂ := by
    rw [he₂]
    exact setAverage_expansion hd (hφ.of_le (by norm_num)) x hε
  have hB₂ : |e₂| ≤ B₂ := by rw [he₂]; exact havg
  exact tugOfWarOp_expansion_bounded p hp hpd ε φ x hS hA hB₁ hB₂

end

end PLaplacian
