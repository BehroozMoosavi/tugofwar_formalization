/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.QuadBound

@[expose] public section

/-!
# Localization of the maximizer

If the maximizer of a test function over a closed ball is y, then its distance
to the point obtained by stepping epsilon in the gradient direction satisfies

  the squared distance is at most two epsilon times the sum of the Hessian
  norm times epsilon squared and the error difference, divided by the gradient
  norm.

With the error difference of order epsilon cubed, this puts the maximizer
within order epsilon to the three halves of the shifted point, which is the
localization the extreme-value expansion needs.

Our own analysis had identified this as the hardest single step in the whole
project. In the event it chains four results already proved: that the shift
has norm epsilon, the bound on the quadratic difference, the conversion of
domination into an inner-product deficit, and the polarization identity
turning that deficit into a distance. The estimate that looked like a project
was a composition.

## Main results

- localize_maximizer
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The localization theorem

Combining `deficit_le`, `quad_diff_le` and `norm_sub_shift_le`: if `y`
maximizes over the closed ball, its distance to the shifted point is
controlled.

The statement carries the error difference as a hypothesis `hE`, since
`taylor_two_bounded` supplies a constant per point and assembling the two into
a single bound is bookkeeping best done where the constants are in hand.
-/

/-- **Localization of the maximizer.**

If `y` maximizes `φ` on the closed ball and the Taylor errors at the two
points differ by at most `E`, then

  `‖y - x - ε ν‖² ≤ 2 ε (‖D²φ x‖ ε² + E) / ‖∇φ x‖`.

With `E` of order `ε³` this is `O(ε³)`, so the maximizer is within
`O(ε^{3/2})` of the shifted point. -/
theorem localize_maximizer {φ : EuclSpace d → ℝ} {x y : EuclSpace d}
    (hx : gradient φ x ≠ 0) {ε E : ℝ} (hε : 0 < ε)
    (hball : ‖y - x‖ ≤ ε)
    (hdom : φ (x + (y - x)) ≥ φ (x + ε • gradDir φ x))
    (hE : taylorErr φ x (y - x) - taylorErr φ x (ε • gradDir φ x) ≤ E) :
    ‖y - x - ε • gradDir φ x‖ ^ 2
      ≤ 2 * ε * ((‖fderiv ℝ (fderiv ℝ φ) x‖ * ε ^ 2 + E)
          / ‖gradient φ x‖) := by
  have hgpos : (0:ℝ) < ‖gradient φ x‖ := norm_pos_iff.2 hx
  -- the shift has norm ε
  have hshift : ‖ε • gradDir φ x‖ ≤ ε := by
    rw [norm_smul, norm_gradDir hx, Real.norm_eq_abs, abs_of_pos hε, mul_one]
  -- the quadratic difference
  have hquad := quad_diff_le (φ := φ) x hball hshift hε
  -- the total bound K
  set K := ‖fderiv ℝ (fderiv ℝ φ) x‖ * ε ^ 2 + E with hK
  have hKbd : (1 / 2) * fderiv ℝ (fderiv ℝ φ) x (y - x) (y - x)
        + taylorErr φ x (y - x)
      - ((1 / 2) * fderiv ℝ (fderiv ℝ φ) x (ε • gradDir φ x)
            (ε • gradDir φ x)
          + taylorErr φ x (ε • gradDir φ x)) ≤ K := by
    rw [hK]
    linarith [hquad, hE]
  -- the deficit
  have hdef := deficit_le hx hdom hKbd
  have hc : ε - inner ℝ (gradDir φ x) (y - x) ≤ K / ‖gradient φ x‖ := by
    rw [le_div_iff₀ hgpos]
    linarith [hdef]
  -- polarization
  exact norm_sub_shift_le x y (norm_gradDir hx) hε hball (by linarith [hc])

end

end PLaplacian
