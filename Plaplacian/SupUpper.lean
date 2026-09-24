/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.SupBound

/-!
# The upper bound on the supremum

The supremum equals the value at the maximizer, and expanding there gives the
linear term as the gradient norm times the inner product with the gradient
direction. Cauchy-Schwarz bounds that inner product by the norm of the
increment, itself at most epsilon.

Together with the lower bound of Plaplacian.SupBound this sandwiches the
supremum: both sides have the same value and linear term, and they differ only
in the quadratic term, one evaluated at the shifted point and the other at the
maximizer. The localization controls that difference, since the maximizer is
close to the shifted point.

## Main results

- sSup_eq_at_max
- sSup_upper_bound
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The upper bound on the supremum

The supremum equals the value at the maximizer `y`. Expanding at `y`,

  `sup = φ x + ‖∇φ x‖ ⟪ν, y-x⟫ + (1/2) D²φ x (y-x, y-x)
           + taylorErr φ x (y-x)`

and Cauchy--Schwarz bounds `⟪ν, y-x⟫` by `‖y-x‖ ≤ ε`. That already gives

  `sup ≤ φ x + ε ‖∇φ x‖ + (1/2) D²φ x (y-x, y-x) + taylorErr φ x (y-x)`,

which combined with the lower bound of `Plaplacian.SupBound` sandwiches the
supremum to within the difference of the two quadratic terms --- and the
localization controls that difference, since `y - x` is close to `ε ν`.
-/

/-- The supremum, expanded at the maximizer. -/
theorem sSup_eq_at_max {φ : EuclSpace d → ℝ} (hφ : Continuous φ)
    {x : EuclSpace d} (hx : gradient φ x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ closedBall x ε,
      sSup (φ '' closedBall x ε)
        = φ x + ‖gradient φ x‖ * inner ℝ (gradDir φ x) (y - x)
          + (1 / 2) * fderiv ℝ (fderiv ℝ φ) x (y - x) (y - x)
          + taylorErr φ x (y - x) := by
  obtain ⟨y, hyMem, hySup⟩ := exists_sSup_closedBall hφ x hε
  refine ⟨y, hyMem, ?_⟩
  rw [hySup]
  have hxy : x + (y - x) = y := by abel
  conv_lhs => rw [← hxy]
  rw [decomp_at φ x (y - x), fderiv_eq_norm_mul_inner hx]

/-- The increment at a point of the closed ball has norm at most `ε`. -/
theorem norm_sub_le_of_mem {x y : EuclSpace d} {ε : ℝ}
    (hy : y ∈ closedBall x ε) : ‖y - x‖ ≤ ε := by
  rw [← dist_eq_norm]
  exact mem_closedBall.1 hy

/-- **The upper bound on the supremum.** -/
theorem sSup_upper_bound {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    {x : EuclSpace d} (hx : gradient φ x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ closedBall x ε,
      sSup (φ '' closedBall x ε)
        ≤ φ x + ε * ‖gradient φ x‖
          + (1 / 2) * fderiv ℝ (fderiv ℝ φ) x (y - x) (y - x)
          + taylorErr φ x (y - x) := by
  obtain ⟨y, hyMem, hyEq⟩ := sSup_eq_at_max hφ.continuous hx hε
  refine ⟨y, hyMem, ?_⟩
  rw [hyEq]
  have hcs : inner ℝ (gradDir φ x) (y - x) ≤ ε := by
    have h1 := inner_gradDir_le hx (y - x)
    have h2 := norm_sub_le_of_mem hyMem
    linarith [h1, h2]
  have hgnn : (0:ℝ) ≤ ‖gradient φ x‖ := norm_nonneg _
  nlinarith [hcs, hgnn]

end

end PLaplacian
