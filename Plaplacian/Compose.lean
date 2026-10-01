/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.UpperEv

/-!
# The composition at a pair

The ball containment, the bound transfer, the near-contact slack and the
expansion combined into one statement at a single pair: given a radius on
which the family minus the test function is below the maximum plus a slack,
and a pair near-contact and positioned within half that radius, the
differential inequality holds with twice the slack.

The radius and both bounds are hypotheses rather than extracted, so the
ordering is visible and the extraction is separate. Three steps remain after
this one: extracting the radius from the local maximum and the upper bound's
neighbourhood, intersecting the frequency with the parameter set, and passing
from the near-contact point to the base point by continuity.

## Main results

- diff_at_good_pair
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The composition

Four radii:

* `r₁` from the local maximum of the relaxed limit;
* `V` from the eventual upper bound, shrunk to a ball of radius `r₂`;
* `r = min r₁ r₂`, so both apply;
* the parameter below `r/2`, for the containment.

The statement below takes the radius and the parameter set as hypotheses,
rather than extracting them, so that the ordering is visible and the
extraction is a separate step.
-/


/-- **The inequality at a pair, with both bounds in place.**

Given a radius on which the family minus the test function is below `M + κ`,
and a pair that is near-contact and positioned within half that radius, the
differential inequality holds with slack. -/
theorem diff_at_good_pair [Nontrivial (EuclSpace d)] {p : ℝ} (hp : 2 ≤ p)
    (hd : 0 < d) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F φ : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ}
    (hφ : ContDiff ℝ 3 φ) (hφb : BddMeas φ)
    {x₀ : EuclSpace d} {r M κ : ℝ} (_hr : 0 < r)
    (hupper : ∀ w ∈ ball x₀ r, ∀ ε : ℝ, 0 < ε →
      u ε w - φ w ≤ M + κ)
    {q : ℝ × EuclSpace d} (hq1 : 0 < q.1)
    (hsmall : q.1 < r / 2 ∧ ‖q.2 - x₀‖ < r / 2)
    (hnear : M - κ ≤ u q.1 q.2 - φ q.2)
    (hu : IsPHarmonious p q.1 Ω F (u q.1))
    (hmem : q.2 ∈ Ω) (hgrad : gradient φ q.2 ≠ 0) :
    ∃ E : ℝ,
      0 ≤ q.1 ^ 2 / (2 * (p + (d : ℝ)))
          * normPLapOf p (gradient φ q.2) (fderiv ℝ (fderiv ℝ φ) q.2)
        + E + 2 * κ := by
  -- the bound transfers to the small ball
  have hball : ∀ w ∈ ball q.2 q.1, u q.1 w - φ w ≤ M + κ := by
    intro w hw
    exact hupper w (ball_subset_of_near hsmall.1 hsmall.2 hw) q.1 hq1
  -- the near-contact gives the value within 2κ of the bound
  have hnear' : (M + κ) - 2 * κ ≤ u q.1 q.2 - φ q.2 := by
    linarith [hnear]
  exact diff_at_pair_approx hp hd hpd hq1 hu hφ hφb hmem hgrad hball hnear'

end

end PLaplacian
