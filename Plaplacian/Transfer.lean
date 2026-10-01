/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Compose

/-!
# From the near-contact point to the base point

The operator at the near-contact point tends to the operator at the base
point along the filter, by continuity away from the singular set composed with
the projection.

## A structural issue this exposes

The inequality at a pair carries the near-contact slack as an additive term.
Dividing by the squared parameter to isolate the operator divides that slack
too, and the slack over the squared parameter does not vanish for a fixed
slack. So the slack cannot be held fixed while the parameter tends to zero: it
must shrink with the parameter, at a rate making the quotient vanish.

That means the near-contact must be sought at a tolerance tied to the
parameter, which is not what the frequency as proved supplies --- there the
tolerance is fixed first and the pairs found afterwards. Whether the frequency
can be restated with the tolerance coupled to the parameter is the question,
and we have not settled it.

## Main results

- tendsto_snd_relax
- tendsto_normPLapOf
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # From the near-contact point to the base point

The step examined least, and so the one most likely to hold a surprise.

The inequality holds at `q.2`, the near-contact point; the predicate wants it
at `x₀`. The operator is continuous away from the singular set, and
`q.2 → x₀` along the filter, so the operator at `q.2` tends to the operator at
`x₀`.

But the inequality is not simply about the operator: it is

  `0 ≤ q.1² / (2(p+d)) * N(q.2) + E + 2κ`

with `N(q.2)` the operator at the near-contact point. Dividing by `q.1²` and
rearranging puts `N(q.2)` on one side, and the limit has to be taken of
`N(q.2)` and of the error quotient together. So what is needed is not just
continuity but that the *combination* converges --- and the error quotient's
limit is along the filter while `N(q.2)`'s is too, so they can be combined.

This probe checks whether the continuity gives the convergence of `N(q.2)`
along the filter, which is the form needed.
-/


/-- The second coordinate tends to the base point along the filter. -/
theorem tendsto_snd_relax (x₀ : EuclSpace d) :
    Filter.Tendsto (fun q : ℝ × EuclSpace d => q.2)
      (relaxFilter x₀) (nhds x₀) := by
  unfold relaxFilter
  exact Filter.tendsto_snd

/-- **The operator at the near-contact point tends to the operator at the
base point.** -/
theorem tendsto_normPLapOf {p : ℝ} {φ : EuclSpace d → ℝ}
    (hφ : ContDiff ℝ 2 φ) {x₀ : EuclSpace d} (hx : gradient φ x₀ ≠ 0) :
    Filter.Tendsto
      (fun q : ℝ × EuclSpace d =>
        normPLapOf p (gradient φ q.2) (fderiv ℝ (fderiv ℝ φ) q.2))
      (relaxFilter x₀)
      (nhds (normPLapOf p (gradient φ x₀)
        (fderiv ℝ (fderiv ℝ φ) x₀))) := by
  have hcont := normPLapOf_continuousAt (p := p) hφ hx
  exact hcont.tendsto.comp (tendsto_snd_relax x₀)

end

end PLaplacian
