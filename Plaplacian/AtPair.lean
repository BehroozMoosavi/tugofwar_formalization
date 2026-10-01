/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Thread2

/-!
# The differential inequality at a pair

At a pair whose point maximizes the difference on the ball of the pair's
parameter, the local comparison and the expansion give the differential
inequality with an error.

The local bound is a hypothesis. Establishing it from the relaxed limit's
local maximum, through the near-contact and the ball containment, is the
remaining analytic step, and keeping it separate is the guard that has worked
throughout.

## Main results

- diff_at_pair
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The differential inequality at a near-contact pair

At a pair that is near-contact and correctly positioned, the bound transfers
to the small ball, the local comparison applies, and the expansion gives the
differential inequality.

The near-contact gives the difference within `δ` of the maximum, not equal to
it, so the comparison is applied with the constant taken to be the value at
the point --- which is what the primed form of the local comparison does, and
why that form was proved.
-/


/-- **The differential inequality at a pair**, given the local bound.

Stated with the bound on the small ball as a hypothesis, since establishing it
from the relaxed limit's local maximum is the remaining analytic step. -/
theorem diff_at_pair [Nontrivial (EuclSpace d)] {p : ℝ} (hp : 2 ≤ p)
    (hd : 0 < d) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F φ : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ}
    {q : ℝ × EuclSpace d} (hq1 : 0 < q.1)
    (hu : IsPHarmonious p q.1 Ω F (u q.1))
    (hφ : ContDiff ℝ 3 φ) (hφb : BddMeas φ)
    (hmem : q.2 ∈ Ω) (hgrad : gradient φ q.2 ≠ 0)
    (hle : ∀ w ∈ ball q.2 q.1, u q.1 w - φ w ≤ u q.1 q.2 - φ q.2) :
    ∃ E : ℝ,
      0 ≤ q.1 ^ 2 / (2 * (p + (d : ℝ)))
          * normPLapOf p (gradient φ q.2) (fderiv ℝ (fderiv ℝ φ) q.2)
        + E := by
  obtain ⟨E, hE⟩ := tugOfWarOp_expansion_final hd p hpd hφ hgrad hq1
  refine ⟨E, ?_⟩
  have hcmp := dpp_comparison_local' hp hq1 hpd hu hφb hmem hle
  rw [hE] at hcmp
  linarith [hcmp]

end

end PLaplacian
