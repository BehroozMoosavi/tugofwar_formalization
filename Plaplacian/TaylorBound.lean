/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Taylor2Deriv

/-!
# The Taylor expansion with an explicit cubic bound

For a C-three function the second-order Taylor error at x in direction z is
bounded by one sixth of a constant depending on z, namely a bound for the
third derivative of the restriction to the segment.

The constant exists by compactness and continuity. Its value is never needed,
and that is what makes this route work. A formula for the third derivative
would require the chain rule through the space of bilinear maps, which carries
ContinuousLinearMap.topologicalSpace rather than the metric topology induced
by the operator norm; Lean does not unify the two, so neither Continuous.norm
nor HasFDerivAt.comp_hasDerivAt is available there. Two earlier routes failed
for exactly that reason.

## Main results

- continuous_deriv_three_restrict, exists_bound_deriv_three
- taylor_two_bounded
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The several-variable expansion with cubic remainder -/

theorem continuous_deriv_three_restrict {φ : EuclSpace d → ℝ}
    (hφ : ContDiff ℝ 3 φ) (x z : EuclSpace d) :
    Continuous (deriv (deriv (deriv (fun t : ℝ => φ (lineMap x z t))))) := by
  have h3 : ContDiff ℝ 3 (fun t : ℝ => φ (lineMap x z t)) :=
    contDiff_restrict_three hφ x z
  have h2 : ContDiff ℝ 2 (deriv (fun t : ℝ => φ (lineMap x z t))) :=
    ContDiff.deriv' h3
  have h1 : ContDiff ℝ 1 (deriv (deriv (fun t : ℝ => φ (lineMap x z t)))) :=
    ContDiff.deriv' h2
  exact h1.continuous_deriv le_rfl

theorem exists_bound_deriv_three {φ : EuclSpace d → ℝ}
    (hφ : ContDiff ℝ 3 φ) (x z : EuclSpace d) :
    ∃ C : ℝ, ∀ t ∈ Icc (0:ℝ) 1,
      |deriv (deriv (deriv (fun s : ℝ => φ (lineMap x z s)))) t| ≤ C := by
  have hcont : Continuous
      (fun t => |deriv (deriv (deriv (fun s : ℝ => φ (lineMap x z s)))) t|) :=
    (continuous_deriv_three_restrict hφ x z).abs
  obtain ⟨t₀, ht₀, hmax⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_isMaxOn
    (by exact ⟨0, by norm_num⟩) hcont.continuousOn
  refine ⟨|deriv (deriv (deriv (fun s : ℝ => φ (lineMap x z s)))) t₀|,
    fun t ht => ?_⟩
  exact hmax ht

/-- **The several-variable expansion with an explicit cubic remainder.**

For each direction `z` there is a constant `C`, depending on `z`, such that
the second-order Taylor error is bounded by `C / 6`. The constant is the
supremum of the third derivative along the segment, which exists by
compactness --- its value is never needed. -/
theorem taylor_two_bounded {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x z : EuclSpace d) :
    ∃ C : ℝ, |φ (x + z) - φ x - fderiv ℝ φ x z
        - (1/2) * fderiv ℝ (fderiv ℝ φ) x z z| ≤ C / 6 := by
  obtain ⟨C, hC⟩ := exists_bound_deriv_three hφ x z
  obtain ⟨ξ, hξ, hres⟩ := taylor_two_deriv
    (fun t : ℝ => φ (lineMap x z t)) (contDiff_restrict_three hφ x z)
  refine ⟨C, ?_⟩
  -- identify the three polynomial terms
  rw [deriv_restrict (hφ.of_le (by norm_num)) x z] at hres
  rw [(hasDerivAt_second_at (hφ.of_le (by norm_num)) x z 0).deriv] at hres
  simp only [lineMap, one_smul, zero_smul, add_zero] at hres
  -- align the bound with the remainder term
  have halign : (fun s : ℝ => φ (lineMap x z s))
      = fun s : ℝ => φ (x + s • z) := by
    funext s; simp [lineMap]
  rw [halign] at hC
  have hinner : (fun t : ℝ => (fderiv ℝ φ (x + t • z)) z)
      = deriv (fun s : ℝ => φ (x + s • z)) := by
    rw [← halign, deriv_restrict (hφ.of_le (by norm_num)) x z]
    funext t; simp [lineMap]
  rw [hinner] at hres
  -- the remainder is bounded
  have hξIcc : ξ ∈ Icc (0:ℝ) 1 := ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
  have hbd := hC ξ hξIcc
  set R := deriv (deriv (deriv fun s : ℝ => φ (x + s • z))) ξ with hR
  have hE : φ (x + z) - φ x - fderiv ℝ φ x z
      - (1/2) * fderiv ℝ (fderiv ℝ φ) x z z = (1/6) * R := by
    linarith [hres]
  rw [hE, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/6)]
  linarith [hbd]

end

end PLaplacian
