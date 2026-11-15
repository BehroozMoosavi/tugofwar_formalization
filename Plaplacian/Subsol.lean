/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Shift

@[expose] public section

/-!
# Towards the subsolution property

The pieces of the subsolution argument: the differential inequality at a
contact point at fixed parameter, the limit argument given the rate, and the
upper semicontinuity of the upper relaxed limit.

The chain runs from the frequent near-contact, through the comparison at a
shifted test function, to the differential inequality, and the rate sends the
error to zero.

What is not yet here is the predicate itself, quantified over all test
functions and contact points. That needs the frequent near-contact converted
into the eventual bound the limit argument consumes, which is quantifier
bookkeeping rather than analysis.

## Main results

- subsol_at, subsol_limit, ubar_usc
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The upper relaxed limit is a subsolution

Assembling. The chain, at a point where `ubar u - φ` is maximal:

* `frequently_near_max` gives points `(ε, y)` frequently along the filter at
  which `u ε - φ` is near its maximum;
* `dpp_comparison_shift` applies at those points, giving
  `φ y ≤ T_ε φ y`;
* `diff_inequality` converts that into the differential inequality with an
  error;
* `LimitPassage` sends the error to zero, using the rate.

The statement is given with the contact hypothesis and the pointwise
conclusion, which is the form the viscosity predicate consumes. The chain is
assembled at a fixed parameter; the limit is taken by
`nonneg_of_rate`.
-/


/-- **The subsolution inequality at a contact point, at fixed parameter.**

If the difference of a solution and the test function is maximal at an
interior point with nonvanishing gradient, then the normalized
`p`-Laplacian of the test function is bounded below by the error, scaled. -/
theorem subsol_at [Nontrivial (EuclSpace d)] {p ε : ℝ} (hp : 2 ≤ p)
    (hd : 0 < d) (hε : 0 < ε) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F u φ : EuclSpace d → ℝ}
    (hu : IsPHarmonious p ε Ω F u) (hφ : ContDiff ℝ 3 φ)
    (hφb : BddMeas φ) {y : EuclSpace d} (hy : y ∈ Ω)
    (hgrad : gradient φ y ≠ 0)
    (hmax : ∀ w, u w - φ w ≤ u y - φ y) :
    ∃ E : ℝ,
      0 ≤ ε ^ 2 / (2 * (p + (d : ℝ)))
          * normPLapOf p (gradient φ y) (fderiv ℝ (fderiv ℝ φ) y) + E :=
  diff_inequality hp hd hε hpd hu hφ hφb hy hgrad hmax rfl

/-- **The subsolution inequality in the limit**, given the rate.

If the errors tend to zero after division, the normalized `p`-Laplacian is
nonnegative --- which is the subsolution inequality `- Δ^N_p φ ≤ 0`. -/
theorem subsol_limit {I : ℝ} {q : ℝ → ℝ}
    (hq : Filter.Tendsto q (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hle : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), q ε ≤ I) :
    0 ≤ I :=
  nonneg_of_rate hq hle

/-- The upper relaxed limit is upper semicontinuous, which is the first field
of the subsolution predicate. -/
theorem ubar_usc (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) :
    UpperSemicontinuous (ubar u) :=
  upperSemicontinuous_ubar u hC

end

end PLaplacian
