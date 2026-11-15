/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.UnifBase

@[expose] public section

/-!
# The Taylor error, uniform in the base point

At any base point the Taylor error equals one sixth of the third derivative of
the restriction at some intermediate parameter. That identity is base-point
generic; it is extracted here from the proof of the cubic rate so that the
uniform bound follows directly rather than by repeating the proof.

Combined with the uniform third-derivative bound, the Taylor error is at most a
constant times the cube of the increment, with the constant serving every base
point near the maximum. That is what lets the expansion error vanish at the
quadratic rate even as the near-maximizer moves with the parameter.

## Main results

- taylorErr_eq_third_deriv
- taylorErr_le_cubic_uniform
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The Taylor error, uniform in the base point

The Taylor error at any base point equals one sixth of the third derivative of
the restriction at some intermediate point. That identity is base-point
generic, and it is extracted here from the proof of the cubic rate so that the
uniform bound follows from it directly, rather than by repeating that proof.

Combined with the uniform third-derivative bound, the Taylor error is at most a
constant times the cube of the increment, the constant serving every base
point near the maximum.
-/


/-- **The Taylor error as a third derivative.** At any base point, for some
intermediate parameter, the error is one sixth of the third derivative of the
restriction there. -/
theorem taylorErr_eq_third_deriv {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (y z : EuclSpace d) :
    ∃ ξ ∈ Ioo (0:ℝ) 1,
      taylorErr φ y z
        = (1 / 6) * deriv (deriv (deriv (fun s : ℝ => φ (y + s • z)))) ξ := by
  obtain ⟨ξ, hξ, hres⟩ := taylor_two_deriv
    (fun s : ℝ => φ (y + s • z)) (by
      have h := contDiff_restrict_three hφ y z
      simpa [lineMap] using h)
  have hd1 : deriv (fun s : ℝ => φ (y + s • z)) 0
      = fderiv ℝ φ y z := by
    have h := hasDerivAt_first (hφ.of_le (by norm_num)) y z 0
    simp only [lineMap, zero_smul, add_zero] at h
    exact h.deriv
  have hd2 : deriv (deriv (fun s : ℝ => φ (y + s • z))) 0
      = fderiv ℝ (fderiv ℝ φ) y z z := by
    have h := hasDerivAt_second_at (hφ.of_le (by norm_num)) y z 0
    simp only [lineMap, zero_smul, add_zero] at h
    have hfun : deriv (fun s : ℝ => φ (y + s • z))
        = fun t => fderiv ℝ φ (y + t • z) z := by
      funext t
      have ht := hasDerivAt_first (hφ.of_le (by norm_num)) y z t
      simp only [lineMap] at ht
      exact ht.deriv
    rw [hfun]
    exact h.deriv
  refine ⟨ξ, hξ, ?_⟩
  unfold taylorErr
  simp only [one_smul, zero_smul, add_zero] at hres
  rw [hd1, hd2] at hres
  linarith [hres]

/-- **The cubic Taylor bound, uniform in the base point.** -/
theorem taylorErr_le_cubic_uniform {φ : EuclSpace d → ℝ}
    (hφ : ContDiff ℝ 3 φ) (x₀ : EuclSpace d) (R : ℝ) :
    ∃ K : ℝ, ∀ y ∈ closedBall x₀ R, ∀ z : EuclSpace d, ‖z‖ ≤ R →
      |taylorErr φ y z| ≤ K * ‖z‖ ^ 3 := by
  obtain ⟨C, hC⟩ := deriv_three_uniform hφ x₀ R
  refine ⟨C, fun y hy z hz => ?_⟩
  obtain ⟨ξ, hξ, herr⟩ := taylorErr_eq_third_deriv hφ y z
  have hbd := hC y hy z hz ξ ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
  rw [herr, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 6)]
  linarith [hbd]

end

end PLaplacian
