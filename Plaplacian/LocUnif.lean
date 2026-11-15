/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.UnifConst

@[expose] public section

/-!
# The localization bound, uniformly

The localization bounds the squared localization distance by a quotient whose
numerator carries the Hessian norm and the error and whose denominator carries
the gradient norm, all at the base point. Replacing each by its uniform
control --- the Hessian and error by upper bounds, the gradient by a lower
bound --- gives a bound independent of the base point.

Each replacement makes the quotient grow, but only for a nonnegative
numerator. Dividing a negative quantity by a smaller positive one makes it
smaller, so the inequality would reverse. The numerator nonnegativity is
therefore a hypothesis, and it is the kind of condition an informal statement
of this step would leave unstated.

## Main results

- localize_rhs_le
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The localization bound, uniformly

`localize_maximizer` bounds the squared localization distance by

  `2 ε (‖D²φ y‖ ε² + E) / ‖∇φ y‖`

at the base point `y`. Replacing each base-point quantity by its uniform
control --- the Hessian norm by an upper bound `H`, the gradient norm by a
lower bound `g`, the error by an upper bound `E₀` --- gives a bound independent
of the base point.

The direction of each replacement needs care. The numerator only grows when
the Hessian and error are replaced by upper bounds, and the denominator only
shrinks when the gradient is replaced by a lower bound, so the quotient only
grows --- but only if the numerator is nonnegative, since dividing a negative
quantity by a smaller positive one makes it smaller, not larger. So the
numerator's nonnegativity is a hypothesis.
-/

/-- **The arithmetic of the uniform localization bound.** -/
theorem localize_rhs_le {ε hy H gy g Ey E₀ : ℝ} (hε : 0 < ε)
    (hH : hy ≤ H) (hg : 0 < g) (hgy : g ≤ gy) (hE : Ey ≤ E₀)
    (hnum : 0 ≤ hy * ε ^ 2 + Ey) :
    2 * ε * ((hy * ε ^ 2 + Ey) / gy)
      ≤ 2 * ε * ((H * ε ^ 2 + E₀) / g) := by
  have hε2 : (0:ℝ) ≤ ε ^ 2 := by positivity
  have hgy0 : 0 < gy := lt_of_lt_of_le hg hgy
  -- the numerator grows
  have hnum' : hy * ε ^ 2 + Ey ≤ H * ε ^ 2 + E₀ := by
    have : hy * ε ^ 2 ≤ H * ε ^ 2 := mul_le_mul_of_nonneg_right hH hε2
    linarith [this, hE]
  -- dividing the smaller numerator by the larger denominator is smaller
  have hdiv : (hy * ε ^ 2 + Ey) / gy ≤ (H * ε ^ 2 + E₀) / g := by
    calc (hy * ε ^ 2 + Ey) / gy
        ≤ (hy * ε ^ 2 + Ey) / g := by
          exact div_le_div_of_nonneg_left hnum hg hgy
      _ ≤ (H * ε ^ 2 + E₀) / g := by
          exact div_le_div_of_nonneg_right hnum' (le_of_lt hg)
  have h2ε : (0:ℝ) ≤ 2 * ε := by linarith
  exact mul_le_mul_of_nonneg_left hdiv h2ε

end

end PLaplacian
