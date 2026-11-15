/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.ApproxCmp

@[expose] public section

/-!
# The eventual upper bound

The comparison needs the difference bounded on the ball about the near-contact
point, by a constant close to the maximum. It comes from the relaxed limit of
the difference being below that maximum plus any slack, which is an eventual
statement along the filter, unpacked here into a set of parameters and a
neighbourhood of the base point.

The bound therefore arrives at the pair level, and applying it on the ball
about the near-contact point requires that ball to lie inside the
neighbourhood. That is the containment lemma again, with the neighbourhood in
place of the local maximum's ball, so the same lemma serves twice and no new
one is needed.

The unpacking reuses a lemma proved for the semicontinuity of the upper
relaxed limit, which is its second use.

## Main results

- exists_upper_bound
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The eventual upper bound

The step not yet verified. The comparison needs

  `u ε w - φ w ≤ c` for all `w ∈ ball y ε`,

with `c` close to the maximum `M = ubar u x₀ - φ x₀`. Where does that come
from?

From the relaxed limit of the difference being below `M + κ`: since
`ubar (u - φ) x₀ = M` and `M < M + κ`, the family minus the test function is
*eventually* below `M + κ` along the filter --- by
`eventually_lt_of_ubar_lt` applied to the difference.

But that gives the bound at the *pair*, i.e. for `(ε, w)` in a product
neighbourhood. The comparison needs it for a fixed `ε` and all `w` in a ball
of radius `ε`. Those differ: the product neighbourhood gives a set `S` of
parameters and a neighbourhood `V` of `x₀`, and the bound for `ε ∈ S` and
`w ∈ V`. If `ball y ε ⊆ V` then it applies --- which is the ball containment
again, with `V` in place of `ball x₀ r`.

So the containment lemma serves twice: once for the local maximum's radius and
once for this neighbourhood. This probe establishes the eventual bound in the
unpacked form.
-/


/-- **The eventual upper bound, unpacked.**

There are a set of parameters and a neighbourhood of the base point on which
the family minus the test function is below the maximum plus any given
slack. -/
theorem exists_upper_bound (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {φ : EuclSpace d → ℝ}
    (hφ : Continuous φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B)
    (x₀ : EuclSpace d) {κ : ℝ} (hκ : 0 < κ) :
    ∃ S ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0), ∃ V ∈ nhds x₀,
      ∀ ε ∈ S, ∀ w ∈ V,
        u ε w - φ w < ubar u x₀ - φ x₀ + κ := by
  have hbd := abs_sub_le_of_bounds u hC hB
  have heq := ubar_sub u hC hφ hB x₀
  have hlt : ubar (fun ε y => u ε y - φ y) x₀
      < ubar u x₀ - φ x₀ + κ := by
    rw [heq]; linarith [hκ]
  exact exists_prod_nhds_of_ubar_lt (fun ε y => u ε y - φ y) hbd x₀ hlt

end

end PLaplacian
