/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.UbarSubEq

/-!
# The contact-point argument

At a maximum of the relaxed limit minus the test function, the family minus
the test function is frequently within any given distance of that maximum.
That is near-contact, and near-contact is the right notion here: a solution is
bounded and Borel but not continuous, so the difference need not attain a
maximum on a closed ball.

The comparison through the operator, however, wants exact contact. The gap is
closed by shifting the test function by a constant, which translation
equivariance leaves the operator indifferent to.

## Main results

- frequently_near_max
- contact_conclusion
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The contact-point argument

If `ubar u - φ` attains a maximum `M` at `x₀`, then `ubar (u - φ) x₀ = M` by
`ubar_sub`, and the filter characterisation gives: for every `δ > 0`, the
difference is frequently above `M - δ` along the filter.

Those are the near-contact points. At each of them the difference is within
`δ` of its supremum, and `dpp_comparison` applies with the constant `M`.
-/


/-- **Frequent near-contact.** At a maximum of the relaxed limit minus the
test function, the family minus the test function is frequently within `δ` of
that maximum. -/
theorem frequently_near_max (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {φ : EuclSpace d → ℝ}
    (hφ : Continuous φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B)
    (x : EuclSpace d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ᶠ q in relaxFilter x,
      ubar u x - φ x - δ < u q.1 q.2 - φ q.2 := by
  have hbd := abs_sub_le_of_bounds u hC hB
  have heq := ubar_sub u hC hφ hB x
  have hlt : ubar u x - φ x - δ
      < ubar (fun ε y => u ε y - φ y) x := by
    rw [heq]; linarith [hδ]
  exact frequently_lt_of_lt_ubar (fun ε y => u ε y - φ y) hbd x hlt

/-- The difference is bounded above by the maximum, when the maximum is
global for the relaxed limit and the family is below its own limit. -/
theorem sub_le_of_global_max (u : ℝ → EuclSpace d → ℝ)
    {φ : EuclSpace d → ℝ} {M : ℝ}
    (hmax : ∀ ε w, u ε w - φ w ≤ M) (ε : ℝ) :
    ∀ w, u ε w - φ w ≤ M := fun w => hmax ε w

/-- **The contact-point conclusion at a fixed parameter.**

If the family minus the test function is globally below `M` and equals `M` at
a point of the domain, the comparison through the operator applies. -/
theorem contact_conclusion {p ε : ℝ} (hp : 2 ≤ p) (hd : 0 < d)
    (hε : 0 < ε) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F u φ : EuclSpace d → ℝ}
    (hu : IsPHarmonious p ε Ω F u) (hφb : BddMeas φ)
    {y : EuclSpace d} (hy : y ∈ Ω) {M : ℝ}
    (hmax : ∀ w, u w - φ w ≤ M) (heq : u y - φ y = M) :
    φ y ≤ tugOfWarOp p ε φ y :=
  dpp_comparison hp hd hε hpd hu hφb hy hmax heq

end

end PLaplacian
