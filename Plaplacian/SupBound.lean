/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.ErrDiff

/-!
# Bounding the extreme values

The supremum over the closed ball dominates the value at the point obtained by
stepping epsilon in the gradient direction, and dually the infimum is
dominated by the value at the point stepping backwards. Substituting the
Taylor expansion at those points gives the first half of the sandwich.

The resulting lower bound on the supremum has the linear term plus epsilon
times the gradient norm, and the upper bound on the infimum has minus the
same. That is the cancellation which produces the infinity Laplacian in the
average of the two.

The other half of the sandwich, the upper bound on the supremum, uses the
localization of the maximizer and is the harder direction.

## Main results

- le_sSup_shift, sInf_shift_le
- sSup_lower_bound
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## Bounding the supremum

The supremum is at least the value at the shifted point, which gives the lower
bound directly from the Taylor expansion:

  `sup ≥ φ x + ε ‖∇φ x‖ + (ε²/2) D²φ x (ν,ν) - |E|`.

For the upper bound, the supremum equals the value at the maximizer `y`, and
the localization puts `y` near `x + ε ν`. Expanding at `y`,

  `sup = φ x + ‖∇φ x‖ ⟪ν, y-x⟫ + (1/2) D²φ x (y-x, y-x) + E`,

and `⟪ν, y-x⟫ ≤ ε` by Cauchy--Schwarz, while the quadratic term differs from
`(ε²/2) D²φ x (ν,ν)` by an amount controlled by the localization.

The lower bound is immediate; we do it first.
-/

/-- The supremum dominates the value at the shifted point. -/
theorem le_sSup_shift {φ : EuclSpace d → ℝ} (hφ : Continuous φ)
    (x : EuclSpace d) {ν : EuclSpace d} (hν : ‖ν‖ = 1) {ε : ℝ}
    (hε : 0 < ε) :
    φ (x + ε • ν) ≤ sSup (φ '' closedBall x ε) := by
  have hbdd : BddAbove (φ '' closedBall x ε) :=
    (isCompact_closedBall x ε).image hφ |>.bddAbove
  exact le_csSup hbdd ⟨x + ε • ν, mem_closedBall_shift x hν hε, rfl⟩

/-- Dually for the infimum. -/
theorem sInf_shift_le {φ : EuclSpace d → ℝ} (hφ : Continuous φ)
    (x : EuclSpace d) {ν : EuclSpace d} (hν : ‖ν‖ = 1) {ε : ℝ}
    (hε : 0 < ε) :
    sInf (φ '' closedBall x ε) ≤ φ (x - ε • ν) := by
  have hbdd : BddBelow (φ '' closedBall x ε) :=
    (isCompact_closedBall x ε).image hφ |>.bddBelow
  exact csInf_le hbdd ⟨x - ε • ν, mem_closedBall_shift_neg x hν hε, rfl⟩

/-- **The lower bound on the supremum.** Taylor at the shifted point. -/
theorem sSup_lower_bound {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    {x : EuclSpace d} (hx : gradient φ x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    φ x + ε * ‖gradient φ x‖
        + (1 / 2) * fderiv ℝ (fderiv ℝ φ) x (ε • gradDir φ x)
            (ε • gradDir φ x)
        + taylorErr φ x (ε • gradDir φ x)
      ≤ sSup (φ '' closedBall x ε) := by
  have hcont : Continuous φ := hφ.continuous
  have h := le_sSup_shift hcont x (norm_gradDir hx) hε
  rw [decomp_at φ x (ε • gradDir φ x), fderiv_eq_at_shift hx] at h
  exact h

end

end PLaplacian
