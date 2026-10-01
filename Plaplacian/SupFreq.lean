/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Exclude

/-!
# The supremum is frequently large

The parameter's own supremum over the closed ball is frequently within any
tolerance of the maximum. Near-contact gives, frequently along the product
filter, a pair whose value is near the maximum; eventually the pair's point
lies in the ball; so the supremum over the ball is near the maximum.

That conclusion mentions only the parameter, and that is the design point: a
property of the parameter alone projects off the product filter. Earlier in
this layer a statement failed for want of exactly this, being phrased as a
function of the parameter while depending in fact on the pair. The supremum is
genuinely a function of the parameter, so the projection applies.

## Main results

- supBall
- frequently_supBall_large
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The supremum is frequently large

The near-maximizer's value clears the annulus bound only if the parameter's
own supremum is large. That supremum is a property of the parameter alone,
which is what lets it be projected off the product filter.

The argument: near-contact gives, frequently along the product filter, a pair
whose value is near the maximum; eventually the pair's point lies in the
ball; so frequently there is a point of the ball with value near the
maximum, whence the supremum over the ball is near the maximum. That last
statement mentions only the parameter, so the frequency projects to the first
factor.
-/


/-- The parameter's supremum over the closed ball. -/
def supBall (u : ℝ → EuclSpace d → ℝ) (φ : EuclSpace d → ℝ)
    (x₀ : EuclSpace d) (r ε : ℝ) : ℝ :=
  sSup ((fun w => u ε w - φ w) '' closedBall x₀ r)

/-- **The supremum is frequently near the maximum.** -/
theorem frequently_supBall_large (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {φ : EuclSpace d → ℝ}
    (hφ : Continuous φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B)
    (x₀ : EuclSpace d) {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) :
    ∃ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ubar u x₀ - φ x₀ - δ < supBall u φ x₀ r ε := by
  -- near-contact, frequently on the product
  have hnear := frequently_near_max u hC hφ hB x₀ hδ
  -- the point eventually in the ball
  have hin : ∀ᶠ q in relaxFilter x₀, q.2 ∈ closedBall x₀ r := by
    have h := eventually_near (x₀ := x₀) (r := 2 * r) (by linarith)
    filter_upwards [h] with q hq
    rw [mem_closedBall, dist_eq_norm]
    have : ‖q.2 - x₀‖ < 2 * r / 2 := hq.2
    linarith [this]
  -- both, frequently
  have hboth := hnear.and_eventually hin
  -- so the supremum is large, a property of the parameter alone
  have hsup : ∃ᶠ q in relaxFilter x₀,
      ubar u x₀ - φ x₀ - δ < supBall u φ x₀ r q.1 := by
    refine hboth.mono ?_
    rintro q ⟨hv, hmem⟩
    have hle := le_sup_on_ball u hC hB x₀ (r := r) (ε := q.1) q.2 hmem
    unfold supBall
    linarith [hv, hle]
  -- project to the parameter
  unfold relaxFilter at hsup
  exact frequently_fst_of_prod hsup

end

end PLaplacian
