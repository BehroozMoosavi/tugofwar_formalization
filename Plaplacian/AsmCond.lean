/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.SuperForm

@[expose] public section

/-!
# The assembly, conditional on the eventual bound

Both predicate inequalities follow from the eventual bound on the error
quotient, taken here as an explicit hypothesis rather than derived in the same
breath.

That separation is deliberate. The quantifier order is the hazard: a statement
of the form for every parameter there exists a multiple is provable for any
quantity and says nothing, while for every multiple there exists a radius is
the content. Taking the bound as a hypothesis makes the order visible and
moves the hazard to the separate task of discharging it.

## Main results

- viscF_le_of_eventually
- le_viscF_of_eventually
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The assembly, conditional on the eventual bound

The hazard in assembling the predicate is the quantifier order: a statement
of the form `∀ ε, ∃ η` is provable for any quantity and says nothing, while
`∀ η, ∃ δ, ∀ ε < δ` is the content.

The remedy used throughout this development is to take the delicate
hypothesis explicitly rather than derive it in the same breath. Here the
hypothesis is the eventual bound: that the error quotient is eventually below
the operator's value. Stated that way, the conclusion follows by the limit
argument, and the vacuity hazard moves to the separate and visible task of
discharging the hypothesis.

This is the same separation as for the expansion with a bounded error, where
the bounds entered as hypotheses rather than being attached to an error
already constructed.
-/


/-- **The subsolution inequality, conditional on the eventual bound.**

If the error quotient tends to zero and is eventually below the operator's
value at the point, then the generator is nonpositive there --- which is the
subsolution inequality. -/
theorem viscF_le_of_eventually {p : ℝ} {φ : EuclSpace d → ℝ}
    {x₀ : EuclSpace d} {q : ℝ → ℝ}
    (hq : Filter.Tendsto q (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hle : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      q ε ≤ normPLapOf p (gradient φ x₀) (fderiv ℝ (fderiv ℝ φ) x₀)) :
    viscF p (gradient φ x₀) (hess φ x₀) ≤ 0 :=
  viscF_le_of_chain (nonneg_of_rate hq hle)

/-- **The supersolution inequality, conditional on the dual bound.** -/
theorem le_viscF_of_eventually {p : ℝ} {φ : EuclSpace d → ℝ}
    {x₀ : EuclSpace d} {q : ℝ → ℝ}
    (hq : Filter.Tendsto q (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hge : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      normPLapOf p (gradient φ x₀) (fderiv ℝ (fderiv ℝ φ) x₀) ≤ q ε) :
    0 ≤ viscF p (gradient φ x₀) (hess φ x₀) :=
  le_viscF_of_chain (nonpos_of_rate hq hge)

/-! The hypotheses are not vacuous: `q` is quantified before the filter
statement, so a witness must serve every small `ε`, and the tendsto condition
fixes its behaviour. Discharging them is the remaining step, and it is the
step where the chain from `frequently_near_max` through
`dpp_comparison_local` to `diff_inequality` is threaded. -/

end

end PLaplacian
