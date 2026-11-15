/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.CubicTaylor

@[expose] public section

/-!
# The Taylor error at a cubic rate

The Taylor error of a test function at an increment of norm at most epsilon is
bounded by a constant times the cube of that norm, with the constant depending
only on the function, the base point and the radius.

This is the Taylor argument repeated with the cubic bound in place of the
opaque constant. The point on the segment lies in the ball, a convex
combination of the centre and a point of the ball being one, so the cubic
bound applies there; the factor one sixth from the Taylor remainder cancels
the six the composition bound produces.

With this the error term of the expansion has an explicit rate in the
increment, which is what a convergence proof consumes.

## Main results

- mem_closedBall_segment
- taylorErr_le_cubic
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The Taylor error at a cubic rate

Repeating the Taylor argument with the cubic bound in place of the opaque
constant. The point on the segment lies in the ball, since a convex
combination of the centre and a point of the ball does, so the cubic bound
applies there; the factor `1/6` from Taylor cancels the `6`.
-/

/-- The segment point lies in the closed ball. -/
theorem mem_closedBall_segment (x z : EuclSpace d) {ε ξ : ℝ}
    (hz : ‖z‖ ≤ ε) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) :
    x + ξ • z ∈ closedBall x ε := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h : x + ξ • z - x = ξ • z := by abel
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg hξ0]
  calc ξ * ‖z‖ ≤ 1 * ‖z‖ := by
        exact mul_le_mul_of_nonneg_right hξ1 (norm_nonneg z)
    _ = ‖z‖ := one_mul _
    _ ≤ ε := hz

/-- **The Taylor error, at a cubic rate.** -/
theorem taylorErr_le_cubic {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x : EuclSpace d) (ε : ℝ) :
    ∃ K : ℝ, ∀ z : EuclSpace d, ‖z‖ ≤ ε →
      |taylorErr φ x z| ≤ K * ‖z‖ ^ 3 := by
  obtain ⟨C, hC⟩ := deriv_three_cubic_bound hφ x ε
  refine ⟨C, fun z hz => ?_⟩
  -- Taylor at order two on the restriction
  obtain ⟨ξ, hξ, hres⟩ := taylor_two_deriv
    (fun s : ℝ => φ (x + s • z)) (by
      have h := contDiff_restrict_three hφ x z
      simpa [lineMap] using h)
  -- the three polynomial terms
  have hd1 : deriv (fun s : ℝ => φ (x + s • z)) 0
      = fderiv ℝ φ x z := by
    have h := hasDerivAt_first (hφ.of_le (by norm_num)) x z 0
    simp only [lineMap, zero_smul, add_zero] at h
    exact h.deriv
  have hd2 : deriv (deriv (fun s : ℝ => φ (x + s • z))) 0
      = fderiv ℝ (fderiv ℝ φ) x z z := by
    have h := hasDerivAt_second_at (hφ.of_le (by norm_num)) x z 0
    simp only [lineMap, zero_smul, add_zero] at h
    have hfun : deriv (fun s : ℝ => φ (x + s • z))
        = fun t => fderiv ℝ φ (x + t • z) z := by
      funext t
      have ht := hasDerivAt_first (hφ.of_le (by norm_num)) x z t
      simp only [lineMap] at ht
      exact ht.deriv
    rw [hfun]
    exact h.deriv
  -- the remainder, bounded cubically
  have hmem : x + ξ • z ∈ closedBall x ε :=
    mem_closedBall_segment x z hz (le_of_lt hξ.1) (le_of_lt hξ.2)
  have hbd := hC z hz ξ hmem
  -- assemble
  have herr : taylorErr φ x z
      = (1 / 6) * deriv (deriv (deriv (fun s : ℝ => φ (x + s • z)))) ξ := by
    unfold taylorErr
    simp only [one_smul, zero_smul, add_zero] at hres
    rw [hd1, hd2] at hres
    linarith [hres]
  rw [herr, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/6)]
  nlinarith [hbd, abs_nonneg
    (deriv (deriv (deriv (fun s : ℝ => φ (x + s • z)))) ξ),
    pow_nonneg (norm_nonneg z) 3]

end

end PLaplacian
