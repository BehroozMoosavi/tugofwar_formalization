/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.GradInner

/-!
# The deficit inequality

The maximizer y over the closed ball satisfies phi at y at least phi at the
shifted point. Expanding both about the centre and using that the derivative
is the gradient norm times the inner product with the direction, the
inner-product deficit is bounded by the difference of the non-linear terms.

The statement carries an abstract bound K rather than the order epsilon
squared estimate, separating the algebra from the analysis, as was done for
the arithmetic core of the uniform convergence argument in Layer 1. The
estimate itself comes from quadratic_le_of_norm_le for the quadratic terms and
taylor_two_bounded for the errors, both of which apply because the increment
and the shift have norm at most epsilon.

One remark on the formalization. The direction of the inequality in K is easy
to get backwards: the deficit is bounded by the terms at the maximizer minus
those at the shifted point, not the reverse. Our first attempt had it
inverted, which yields a lower bound rather than an upper one and is useless
here. The failure of linarith was correct and caught the error immediately.

## Main results

- decomp_at
- deficit_le
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The deficit

`y` maximizes `φ` on the closed ball, so `φ y ≥ φ (x + ε ν)`. Writing
`w = y - x` and expanding both about `x`:

  `Dφ x w + (1 / 2) D²φ x (w,w) + E w ≥ ε ‖∇φ x‖ + (1 / 2) D²φ x (εν,εν) + E (εν)`

with `Dφ x w = ‖∇φ x‖ ⟪ν, w⟫`. Rearranged,

  `‖∇φ x‖ (ε - ⟪ν, w⟫)
     ≤ (1 / 2)[D²φ x (w,w) - D²φ x (εν,εν)] + E w - E (εν)`.

Both `w` and `εν` have norm at most `ε`, so the quadratic difference is
`O(ε²)` by `quadratic_le_of_norm_le`, and the error terms are `O(ε³)` by
`taylor_two_bounded`. Dividing by the nonzero `‖∇φ x‖` gives the deficit.

This file assembles the rearrangement. The `O(ε²)` bookkeeping is stated in
terms of an abstract bound `K` on the right-hand side, so that the algebra is
separated from the estimates.
-/

/-- The Taylor decomposition, at a point of the ball. -/
theorem decomp_at (φ : EuclSpace d → ℝ) (x w : EuclSpace d) :
    φ (x + w) = φ x + fderiv ℝ φ x w
      + (1 / 2) * fderiv ℝ (fderiv ℝ φ) x w w + taylorErr φ x w := by
  exact taylor_decomp φ x w

/-- **The deficit inequality, in abstract form.**

If the maximizer's value dominates the shifted point's, and the quadratic and
error terms on both sides are bounded by `K` in total, then the inner-product
deficit is at most `K` divided by the gradient norm. -/
theorem deficit_le {φ : EuclSpace d → ℝ} {x y : EuclSpace d}
    (hx : gradient φ x ≠ 0) {ε K : ℝ}
    (hdom : φ (x + (y - x)) ≥ φ (x + ε • gradDir φ x))
    (hK : (1 / 2) * fderiv ℝ (fderiv ℝ φ) x (y - x) (y - x)
            + taylorErr φ x (y - x)
          - ((1 / 2) * fderiv ℝ (fderiv ℝ φ) x (ε • gradDir φ x)
                (ε • gradDir φ x)
              + taylorErr φ x (ε • gradDir φ x)) ≤ K) :
    ‖gradient φ x‖ * (ε - inner ℝ (gradDir φ x) (y - x)) ≤ K := by
  rw [decomp_at φ x (y - x), decomp_at φ x (ε • gradDir φ x)] at hdom
  rw [fderiv_eq_norm_mul_inner hx (y - x),
      fderiv_eq_at_shift hx ε] at hdom
  have hdist : ‖gradient φ x‖ * (ε - inner ℝ (gradDir φ x) (y - x))
      = ‖gradient φ x‖ * ε
        - ‖gradient φ x‖ * inner ℝ (gradDir φ x) (y - x) := by ring
  rw [hdist]
  have hcomm : ε * ‖gradient φ x‖ = ‖gradient φ x‖ * ε := mul_comm _ _
  rw [hcomm] at hdom
  linarith [hdom, hK]

end

end PLaplacian
