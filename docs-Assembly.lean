/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.C2Diff

/-!
# The predicate assembly: route and statement

NOT PART OF THE BUILD. This file records the remaining step of the
subsolution half of Layer 4, with its route and its hazard, so that it can be
written from a clear starting point.

## The target

  `IsViscositySubsolution p Ω 0 (ubar u)`

has three fields. Two are available:

* `usc` is `ubar_usc`, proved;
* `singular`, the case of vanishing gradient, is supplied by
  `quad_le_lamMax_ball` of Plaplacian.Singular, modulo the same assembly as
  the regular case.

The remaining field is `regular`:

  `∀ φ, ContDiff ℝ 2 φ → ∀ x₀ ∈ Ω, IsLocalMax (ubar u - φ) x₀ →
     gradient φ x₀ ≠ 0 → viscF p (gradient φ x₀) (hess φ x₀) ≤ 0`.

## The route, with every input named

Fix `φ` of class `C²`, `x₀ ∈ Ω`, a local maximum, and a nonvanishing
gradient. Then:

1. `exists_radius_of_isLocalMax` turns the local maximum into a radius `r`
   with `ubar u - φ ≤ (ubar u - φ) x₀` on `ball x₀ r`.

2. `ubar_sub` rewrites that as a statement about
   `ubar (fun ε y => u ε y - φ y)`, the relaxed limit of the difference, which
   needs `φ` continuous and bounded. Continuity is from `C²`; boundedness must
   be a hypothesis or `φ` must be modified far away, and the operator's
   locality means modification far away is harmless.

3. `frequently_near_max` gives, for each `δ > 0`, points `(ε, y)` frequently
   along `relaxFilter x₀` with `u ε y - φ y` within `δ` of the maximum.

4. At such a point, `dpp_comparison_local'` applies --- it needs the bound on
   `ball y ε`, which follows from the bound on `ball x₀ r` once `ε` is small
   enough that `ball y ε ⊆ ball x₀ r`, i.e. `ε < r/2` and `y` within `r/2` of
   `x₀`. Both hold eventually along the filter. Conclusion:
   `φ y ≤ tugOfWarOp p ε φ y`.

5. `diff_inequality` converts that into
   `0 ≤ ε²/(2(p+d)) * normPLapOf p (gradient φ y) (hess φ y) + E`.
   NOTE: this is at `y`, not at `x₀`. The Hessian and gradient are evaluated
   at the near-contact point, and `y → x₀` only in the limit. Passing to `x₀`
   needs continuity of `gradient φ` and `hess φ`, which `C²` supplies.

6. `normPLap_mul_ge` clears the denominator, `taylorErr_le_on_ball_c2` bounds
   the error at `C²`, `tendsto_err_quotient` sends the quotient to zero, and
   `nonneg_of_rate` concludes `0 ≤ normPLapOf p (gradient φ x₀) (hess φ x₀)`.

7. `viscF_le_of_chain` is the conclusion.

## The hazard

Step 6 is where a vacuous statement is easiest to write. The order must be

  `∀ η > 0, ∃ δ > 0, ∀ ε < δ, (bound involving η)`

and NOT

  `∀ ε > 0, ∃ η > 0, (bound involving η)`,

which is provable for any quantity by taking `η` large, and says nothing. The
test: does `δ` depend on `η` only, or does it depend on `ε`? If the latter,
the statement is empty.

We have written the vacuous form twice in this development
(see the finding on bounds versus rates), both times when assembling a
conclusion under time pressure, and caught the second only on reading it
back. The guard is to write the quantifier order out before the proof, as
above, and to check the dependency of each witness.

## A further subtlety, now resolved

Step 5 evaluates the operator at `y`, step 7 wants it at `x₀`. The
intermediate step --- that `normPLapOf p (gradient φ y) (hess φ y)` tends to
`normPLapOf p (gradient φ x₀) (hess φ x₀)` as `y → x₀` --- needs continuity
of `normPLapOf` in its arguments. That is true but it involves
`infLaplacianOf`, which divides by the gradient norm, so it holds only where
the gradient does not vanish. Since the regular case assumes exactly that, it
is available. That lemma is now proved as normPLapOf_continuousAt in
Plaplacian.OpContFull, so every input to the assembly exists and what remains
is the quantifier threading of step 6 alone.

## Statement

The target, stated so that it can be filled in directly.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-- **The regular field of the subsolution predicate.** -/
theorem ubar_regular [Nontrivial (EuclSpace d)] (hd : 0 < d) {p : ℝ}
    (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ}
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε))
    (hC : ∀ ε y, |u ε y| ≤ C)
    (φ : EuclSpace d → ℝ) (hφ : ContDiff ℝ 2 φ) (hφb : BddMeas φ)
    {x₀ : EuclSpace d} (hx₀ : x₀ ∈ Ω)
    (hmax : IsLocalMax (fun y => ubar u y - φ y) x₀)
    (hgrad : gradient φ x₀ ≠ 0) :
    viscF p (gradient φ x₀) (hess φ x₀) ≤ 0 := by
  sorry

end

end PLaplacian
