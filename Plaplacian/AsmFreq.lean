/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.FreqRate

/-!
# The conditional assembly, with a frequent bound

The earlier conditional form took an eventual bound; the contact points supply
only a frequent one. Restated with the frequency, the hypothesis matches what
near-contact produces.

That correction matters. Had the predicate been assembled with the eventual
hypothesis, the theorem would have looked complete while resting on something
the chain cannot supply, and the gap would have shown only when someone tried
to use it.

What remains is to discharge the frequency: that the error quotient is
frequently below the operator value. Proved theorems sit on both sides of that
step, with matching quantifiers.

## Main results

- viscF_le_of_frequently
- le_viscF_of_frequently
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The conditional assembly, with a frequent bound

`viscF_le_of_eventually` took an eventual bound; the contact points supply
only a frequent one. Restating with the frequency, the hypothesis now matches
what `frequently_near_max` produces, and the gap in the chain is closed.

What still has to be discharged is the frequency itself: that the error
quotient is frequently below the operator's value. That is where the chain
from near-contact through the local comparison to the differential inequality
is threaded, and it remains the one outstanding step.
-/


/-- **The subsolution inequality, conditional on a frequent bound.** -/
theorem viscF_le_of_frequently {p : ℝ} {φ : EuclSpace d → ℝ}
    {x₀ : EuclSpace d} {q : ℝ → ℝ}
    (hq : Filter.Tendsto q (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hfreq : ∃ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      q ε ≤ normPLapOf p (gradient φ x₀) (fderiv ℝ (fderiv ℝ φ) x₀)) :
    viscF p (gradient φ x₀) (hess φ x₀) ≤ 0 :=
  viscF_le_of_chain (nonneg_of_frequently hq hfreq)

/-- **The supersolution inequality, conditional on the dual frequency.** -/
theorem le_viscF_of_frequently {p : ℝ} {φ : EuclSpace d → ℝ}
    {x₀ : EuclSpace d} {q : ℝ → ℝ}
    (hq : Filter.Tendsto q (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hfreq : ∃ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      normPLapOf p (gradient φ x₀) (fderiv ℝ (fderiv ℝ φ) x₀) ≤ q ε) :
    0 ≤ viscF p (gradient φ x₀) (hess φ x₀) :=
  le_viscF_of_chain (nonpos_of_frequently hq hfreq)

end

end PLaplacian
