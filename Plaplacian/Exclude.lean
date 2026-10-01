/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.UnifEv

/-!
# Excluding the near-maximizer from the annulus

At a single parameter, with every input a hypothesis: if the family minus the
test function is below a bound on the annulus, and a point of the closed ball
has value at least that bound, the point is not in the annulus and so lies
within the inner radius. A near-maximizer whose value clears the bound is
therefore near the base point.

The step is kept per-parameter and free of filters. The frequency along the
filter and the choice of near-maximizer as a function of the parameter are
separate, so that this step has no quantifiers to misorder.

## Main results

- mem_ball_of_not_annulus
- near_of_above
- nearmax_in_ball
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # Excluding the near-maximizer from the annulus

The third step of the annulus route, at a single parameter and with every
input a hypothesis. If the family minus the test function is below a bound on
the annulus, and a point of the closed ball has value at least that bound,
then the point is not in the annulus, and so lies within the inner radius.

Kept per-parameter and pure. The frequency along the filter, and the choice of
near-maximizer as a function of the parameter, are separate, so that the
quantifiers of this step are visible and cannot be misordered.
-/

/-- A point of the closed ball outside the annulus lies within the inner
radius. -/
theorem mem_ball_of_not_annulus {x₀ y : EuclSpace d} {ρ r : ℝ}
    (hy : y ∈ closedBall x₀ r) (hna : y ∉ annulus x₀ ρ r) :
    y ∈ ball x₀ ρ := by
  unfold annulus at hna
  by_contra hb
  exact hna ⟨hy, hb⟩

/-- **The exclusion.** A point of the closed ball whose value is at least the
annulus bound lies within the inner radius. -/
theorem near_of_above {u : EuclSpace d → ℝ} {φ : EuclSpace d → ℝ}
    {x₀ y : EuclSpace d} {ρ r a : ℝ}
    (hann : ∀ w ∈ annulus x₀ ρ r, u w - φ w < a)
    (hy : y ∈ closedBall x₀ r) (habove : a ≤ u y - φ y) :
    y ∈ ball x₀ ρ := by
  refine mem_ball_of_not_annulus hy ?_
  intro hya
  have := hann y hya
  linarith [this, habove]

/-- **The near-maximizer is near the base point**, at a single parameter.

If the near-maximizer's value exceeds its supremum less the tolerance, and
that exceeds the annulus bound, the near-maximizer lies within the inner
radius. -/
theorem nearmax_in_ball {u : EuclSpace d → ℝ} {φ : EuclSpace d → ℝ}
    {x₀ y : EuclSpace d} {ρ r a S τ : ℝ}
    (hann : ∀ w ∈ annulus x₀ ρ r, u w - φ w < a)
    (hy : y ∈ closedBall x₀ r)
    (hnear : S - τ < u y - φ y) (hclear : a ≤ S - τ) :
    y ∈ ball x₀ ρ :=
  near_of_above hann hy (by linarith [hnear, hclear])

end

end PLaplacian
