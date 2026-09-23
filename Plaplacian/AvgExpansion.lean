/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.IterFDeriv
import Plaplacian.AvgTerms

/-!
# The average expansion

The average of a test function over a ball equals its value at the centre,
plus epsilon squared over twice d plus two times the Laplacian, plus the
average of the Taylor error.

This is the first half of the asymptotic expansion of the step operator, and
the theorem for which the moment computations of Plaplacian.BallMoments were
built. The linear term drops out by the odd moments; the quadratic term
becomes the Laplacian by the second moments at arbitrary radius.

The error is left as an average rather than estimated, so the statement is
exact. It is of order epsilon cubed, by the uniform third-derivative bound of
Plaplacian.IterFDeriv, and so contributes nothing at order epsilon squared.

## Main results

- taylorErr, taylor_decomp
- setAverage_expansion
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The average expansion -/

def taylorErr (φ : EuclSpace d → ℝ) (x z : EuclSpace d) : ℝ :=
  φ (x + z) - φ x - fderiv ℝ φ x z
    - (1/2) * fderiv ℝ (fderiv ℝ φ) x z z

theorem taylor_decomp (φ : EuclSpace d → ℝ) (x z : EuclSpace d) :
    φ (x + z) = φ x + fderiv ℝ φ x z
      + (1/2) * fderiv ℝ (fderiv ℝ φ) x z z + taylorErr φ x z := by
  unfold taylorErr; ring

theorem continuous_linear_term (φ : EuclSpace d → ℝ) (x : EuclSpace d) :
    Continuous (fun z : EuclSpace d => fderiv ℝ φ x z) :=
  (fderiv ℝ φ x).continuous

theorem continuous_quad_term (φ : EuclSpace d → ℝ) (x : EuclSpace d) :
    Continuous (fun z : EuclSpace d =>
      (1/2) * fderiv ℝ (fderiv ℝ φ) x z z) := by
  have h : Continuous (fun z : EuclSpace d =>
      fderiv ℝ (fderiv ℝ φ) x z z) := by
    exact (fderiv ℝ (fderiv ℝ φ) x).continuous.clm_apply continuous_id
  exact continuous_const.mul h

theorem integrableOn_linear (φ : EuclSpace d → ℝ) (x : EuclSpace d) (ε : ℝ) :
    MeasureTheory.IntegrableOn (fun z : EuclSpace d => fderiv ℝ φ x z)
      (ball (0 : EuclSpace d) ε) :=
  ((continuous_linear_term φ x).continuousOn.integrableOn_compact
    (isCompact_closedBall _ _)).mono_set ball_subset_closedBall

theorem integrableOn_quad (φ : EuclSpace d → ℝ) (x : EuclSpace d) (ε : ℝ) :
    MeasureTheory.IntegrableOn
      (fun z : EuclSpace d => (1/2) * fderiv ℝ (fderiv ℝ φ) x z z)
      (ball (0 : EuclSpace d) ε) :=
  ((continuous_quad_term φ x).continuousOn.integrableOn_compact
    (isCompact_closedBall _ _)).mono_set ball_subset_closedBall

theorem continuous_taylorErr {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x : EuclSpace d) :
    Continuous (fun z : EuclSpace d => taylorErr φ x z) := by
  unfold taylorErr
  have h1 : Continuous (fun z : EuclSpace d => φ (x + z)) :=
    (hφ.continuous).comp (continuous_const.add continuous_id)
  exact ((h1.sub continuous_const).sub (continuous_linear_term φ x)).sub
    (continuous_quad_term φ x)

theorem integrableOn_taylorErr {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x : EuclSpace d) (ε : ℝ) :
    MeasureTheory.IntegrableOn (fun z => taylorErr φ x z)
      (ball (0 : EuclSpace d) ε) :=
  ((continuous_taylorErr hφ x).continuousOn.integrableOn_compact
    (isCompact_closedBall _ _)).mono_set ball_subset_closedBall

/-! ### The expansion -/

/-- **The average expansion with an explicit error term.**

The average of `φ` over a ball equals the value at the centre plus the
quadratic term, plus the average of the Taylor error. The linear term drops
out by the odd moments; the quadratic term is the Laplacian by the second
moments.

The error term is left as an average rather than estimated, so that the
statement is exact. Bounding it is `setAverage_taylorErr_le` below. -/
theorem setAverage_expansion [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ) (x : EuclSpace d) {ε : ℝ}
    (hε : 0 < ε) :
    (⨍ y in ball x ε, φ y)
      = φ x + ε ^ 2 / (2 * ((d : ℝ) + 2)) * laplacianOf (hess φ x)
        + ⨍ z in ball (0 : EuclSpace d) ε, taylorErr φ x z := by
  rw [setAverage_ball_translate φ x ε]
  have hdec : (fun z : EuclSpace d => φ (x + z))
      = fun z => φ x + fderiv ℝ φ x z
        + (1/2) * fderiv ℝ (fderiv ℝ φ) x z z + taylorErr φ x z := by
    funext z
    exact taylor_decomp φ x z
  rw [hdec]
  -- split the average across the four terms
  have hsplit : (⨍ z in ball (0 : EuclSpace d) ε,
        (φ x + fderiv ℝ φ x z
          + (1/2) * fderiv ℝ (fderiv ℝ φ) x z z + taylorErr φ x z))
      = (⨍ z in ball (0 : EuclSpace d) ε, φ x)
        + (⨍ z in ball (0 : EuclSpace d) ε, fderiv ℝ φ x z)
        + (⨍ z in ball (0 : EuclSpace d) ε,
            (1/2) * fderiv ℝ (fderiv ℝ φ) x z z)
        + (⨍ z in ball (0 : EuclSpace d) ε, taylorErr φ x z) := by
    have hc : MeasureTheory.IntegrableOn (fun _ : EuclSpace d => φ x)
        (ball (0 : EuclSpace d) ε) := integrableOn_const
    have hl := integrableOn_linear φ x ε
    have hq := integrableOn_quad φ x ε
    have he := integrableOn_taylorErr hφ x ε
    rw [show (fun z : EuclSpace d => φ x + fderiv ℝ φ x z
          + (1/2) * fderiv ℝ (fderiv ℝ φ) x z z + taylorErr φ x z)
        = ((fun _ : EuclSpace d => φ x) + (fun z => fderiv ℝ φ x z)
            + (fun z => (1/2) * fderiv ℝ (fderiv ℝ φ) x z z))
          + (fun z => taylorErr φ x z) from rfl]
    rw [MeasureTheory.setAverage_add (((hc.add hl).add hq)) he,
        MeasureTheory.setAverage_add (hc.add hl) hq,
        MeasureTheory.setAverage_add hc hl]
  rw [hsplit, setAverage_const_ball (φ x) 0 hε,
      setAverage_fderiv_eq_zero φ x ε,
      setAverage_hess_term hd φ x hε]
  ring

end

end PLaplacian
