/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.QuadAverage
public import Plaplacian.Taylor2D

@[expose] public section

/-!
# The clean terms of the average expansion

Integrating the second-order Taylor expansion over a ball produces four
terms: the value, the linear term, the quadratic term, and the Lagrange
remainder. The first three are computed here; the remainder is harder, because
its Lagrange point depends on the integration variable, and is treated
separately.

The linear term vanishes by the odd moments of Plaplacian.BallMoments. Those
are stated for the inner product against a vector, while Taylor produces a
continuous linear functional applied to the increment; the two are identified
by inner_gradient_left, since the gradient is the Riesz representative.

The quadratic term is setAverage_quadratic of Plaplacian.QuadAverage, after
pulling out the factor one half.

## A fourth missing set-average lemma

setAverage_const_mul, pulling a scalar out of an average, is not in Mathlib.
Neither is setAverage_mul_const, nor setAverage_finsetSum, nor
setAverage_mono. Four omissions from the same corner of the library: the
set-average API is visibly thinner than the integral API beneath it, and the
four together would make a natural upstream contribution.

## Main results

- setAverage_const_mul
- setAverage_fderiv_eq_zero: the linear term vanishes.
- setAverage_hess_term: the quadratic term.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## Missing set-average API

A fourth omission: Mathlib has no lemma pulling a scalar out of a set average.
With `setAverage_mono`, `setAverage_mul_const` and `setAverage_finsetSum`, that
is four gaps in the same corner of the library.
-/

/-- Pulling a scalar out of a set average on the left. -/
theorem setAverage_const_mul (c : ℝ) (f : EuclSpace d → ℝ)
    (s : Set (EuclSpace d)) :
    (⨍ z in s, c * f z) = c * ⨍ z in s, f z := by
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq,
      MeasureTheory.integral_const_mul, smul_eq_mul, smul_eq_mul]
  ring

/-! ## The linear term

`integral_inner_ball_eq_zero` is stated for `inner ℝ x z`; Taylor produces
`fderiv ℝ φ x z`. The bridge is `inner_gradient_left`, which identifies the
functional with the inner product against the gradient.
-/

/-- The derivative applied to `z`, as an inner product. -/
theorem fderiv_eq_inner_gradient (φ : EuclSpace d → ℝ) (x z : EuclSpace d) :
    fderiv ℝ φ x z = inner ℝ (gradient φ x) z :=
  (inner_gradient_left).symm

/-- **The linear term vanishes.** -/
theorem setAverage_fderiv_eq_zero (φ : EuclSpace d → ℝ) (x : EuclSpace d)
    (ε : ℝ) :
    (⨍ z in ball (0 : EuclSpace d) ε, fderiv ℝ φ x z) = 0 := by
  have h : (fun z : EuclSpace d => fderiv ℝ φ x z)
      = fun z : EuclSpace d => inner ℝ (gradient φ x) z := by
    funext z
    exact fderiv_eq_inner_gradient φ x z
  rw [h, MeasureTheory.setAverage_eq,
      integral_inner_ball_eq_zero (gradient φ x) ε]
  simp

/-! ## The quadratic term -/

/-- **The quadratic term.** -/
theorem setAverage_hess_term [Nontrivial (EuclSpace d)] (hd : 0 < d)
    (φ : EuclSpace d → ℝ) (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    (⨍ z in ball (0 : EuclSpace d) ε,
        (1/2) * fderiv ℝ (fderiv ℝ φ) x z z)
      = ε ^ 2 / (2 * ((d : ℝ) + 2)) * laplacianOf (hess φ x) := by
  rw [setAverage_const_mul (1/2) (fun z => fderiv ℝ (fderiv ℝ φ) x z z),
      setAverage_quadratic hd (fderiv ℝ (fderiv ℝ φ) x) hε]
  unfold hess
  have hd2 : ((d : ℝ) + 2) ≠ 0 := by positivity
  field_simp

end

end PLaplacian
