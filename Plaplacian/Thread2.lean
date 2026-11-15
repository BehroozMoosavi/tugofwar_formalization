/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.BallCont

@[expose] public section

/-!
# The frequency with the ball containment

The near-contact frequency intersected with the eventual smallness gives
pairs that are both near-contact and positioned so that the ball about the
point lies in the ball about the base point. The bound then transfers from the
larger ball to the smaller, which is what the local comparison consumes.

This step had been the obstacle. It came apart into one application of a
library lemma to two already-proved facts, because the geometry was isolated
from the filter work in the preceding file, so neither had to be reasoned
about while holding the other. That separation is the guard that has worked
throughout, and it is why this went in one attempt.

## Main results

- frequently_near_and_small
- containment_of_near, bound_transfer
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The frequency with the ball containment

Intersecting the near-contact frequency with the eventual smallness gives a
frequency of pairs that are both near-contact *and* positioned so that the
ball containment holds.

That is the step the threading needs, and it is one application of
`Frequently.and_eventually`.
-/


/-- **Near-contact with the containment.**

Frequently along the filter, the pair is near-contact and the parameter and
displacement are each below half the radius --- so the ball about the point is
contained in the ball about the base point. -/
theorem frequently_near_and_small (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {φ : EuclSpace d → ℝ}
    (hφ : Continuous φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B)
    (x₀ : EuclSpace d) {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) :
    ∃ᶠ q in relaxFilter x₀,
      (ubar u x₀ - φ x₀ - δ < u q.1 q.2 - φ q.2)
      ∧ (q.1 < r / 2 ∧ ‖q.2 - x₀‖ < r / 2) := by
  exact (frequently_near_max u hC hφ hB x₀ hδ).and_eventually
    (eventually_near (x₀ := x₀) hr)

/-- At such a pair, the ball containment holds. -/
theorem containment_of_near {x₀ : EuclSpace d} {q : ℝ × EuclSpace d}
    {r : ℝ} (h : q.1 < r / 2 ∧ ‖q.2 - x₀‖ < r / 2) :
    ball q.2 q.1 ⊆ ball x₀ r :=
  ball_subset_of_near h.1 h.2

/-- And the bound transfers: a bound on the larger ball gives one on the
smaller. -/
theorem bound_transfer {x₀ : EuclSpace d} {q : ℝ × EuclSpace d} {r : ℝ}
    (h : q.1 < r / 2 ∧ ‖q.2 - x₀‖ < r / 2)
    {f : EuclSpace d → ℝ} {c : ℝ}
    (hbd : ∀ w ∈ ball x₀ r, f w ≤ c) :
    ∀ w ∈ ball q.2 q.1, f w ≤ c := by
  intro w hw
  exact hbd w (containment_of_near h hw)

end

end PLaplacian
