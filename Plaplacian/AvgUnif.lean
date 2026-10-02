/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.UnifErr

/-!
# The average error, uniform in the base point

The average half of the expansion carries its error as the average of the
Taylor error over the ball. With the Taylor error bounded uniformly in the base
point, so is its average: at most a constant times the cube of the radius, the
constant serving every base point near the maximum and every small radius.

The bound is two-sided, obtained by averaging the pointwise upper and lower
bounds separately against constant functions.

## Main results

- avgErr_uniform
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The average error, uniform in the base point

The average half of the expansion carries its error as the average of the
Taylor error over the ball. With the Taylor error bounded uniformly in the base
point, so is its average: it is at most a constant times the cube of the
radius, the constant serving every base point near the maximum.

The bound is two-sided, by averaging the upper and lower bounds separately
against the constant function.
-/


/-- **The average error, uniform in the base point.** -/
theorem avgErr_uniform {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x₀ : EuclSpace d) (R : ℝ) :
    ∃ K : ℝ, ∀ y ∈ closedBall x₀ R, ∀ ε : ℝ, 0 < ε → ε ≤ R →
      |⨍ z in ball (0 : EuclSpace d) ε, taylorErr φ y z| ≤ K * ε ^ 3 := by
  obtain ⟨K₀, hK₀⟩ := taylorErr_le_cubic_uniform hφ x₀ R
  set K := max K₀ 0 with hK
  refine ⟨K, fun y hy ε hε hεR => ?_⟩
  have hKnn : (0:ℝ) ≤ K := le_max_right _ _
  have hKge : K₀ ≤ K := le_max_left _ _
  -- the pointwise bound on the ball
  have hpt : ∀ z ∈ ball (0 : EuclSpace d) ε,
      |taylorErr φ y z| ≤ K * ε ^ 3 := by
    intro z hz
    have hzn : ‖z‖ < ε := by
      rw [mem_ball, dist_zero_right] at hz; exact hz
    have hzR : ‖z‖ ≤ R := le_trans (le_of_lt hzn) hεR
    have h1 := hK₀ y hy z hzR
    have hz3 : ‖z‖ ^ 3 ≤ ε ^ 3 := by
      have h0 : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
      nlinarith [hzn, h0, hε, sq_nonneg (‖z‖ - ε), sq_nonneg (‖z‖ + ε)]
    have hz3nn : (0:ℝ) ≤ ‖z‖ ^ 3 := by positivity
    nlinarith [h1, hz3, hKge, hKnn, hz3nn]
  -- integrability
  have hint := integrableOn_taylorErr (hφ.of_le (by norm_num)) y ε
  have hconst : MeasureTheory.IntegrableOn
      (fun _ : EuclSpace d => K * ε ^ 3) (ball (0 : EuclSpace d) ε) :=
    integrableOn_const
  have hconstn : MeasureTheory.IntegrableOn
      (fun _ : EuclSpace d => -(K * ε ^ 3)) (ball (0 : EuclSpace d) ε) :=
    integrableOn_const
  -- the two sides
  have hup : (⨍ z in ball (0 : EuclSpace d) ε, taylorErr φ y z)
      ≤ K * ε ^ 3 := by
    have h := setAverage_mono measurableSet_ball hint hconst
      (fun z hz => le_of_abs_le (hpt z hz))
    rwa [setAverage_const_ball (K * ε ^ 3) 0 hε] at h
  have hlo : -(K * ε ^ 3)
      ≤ ⨍ z in ball (0 : EuclSpace d) ε, taylorErr φ y z := by
    have h := setAverage_mono measurableSet_ball hconstn hint
      (fun z hz => (abs_le.1 (hpt z hz)).1)
    rwa [setAverage_const_ball (-(K * ε ^ 3)) 0 hε] at h
  rw [abs_le]
  exact ⟨hlo, hup⟩

end

end PLaplacian
