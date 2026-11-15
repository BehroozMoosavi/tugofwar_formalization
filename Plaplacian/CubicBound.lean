/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Expansion

@[expose] public section

/-!
# The cubic bound, with the increment exhibited

The Taylor bound of the expansion hides the dependence on the increment: its
constant bounds the third derivative of the restriction to a line, which
already contains three factors of the increment. A rate for the error term
needs that dependence made explicit.

The flat representation supplies it. The uniform bound over a closed ball,
together with the multilinear operator-norm inequality, gives the third
derivative evaluated at the increment three times bounded by a constant times
the cube of its norm, with the constant independent of the increment.

This is the clearest vindication of the finding on the two representations.
The curried tower cannot express this bound at all, having no usable operator
norm; the flat one gives it in a single application of le_opNorm. Three routes
to the remainder failed on that distinction before it was understood.

## Main results

- iteratedFDeriv_three_le
- exists_cubic_bound
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The cubic bound, via the flat representation

`taylor_two_bounded` hides the dependence on the increment: its constant
bounds the third derivative of `t ↦ φ (x + t z)`, which already contains three
factors of `z`. A rate needs that dependence exhibited.

The flat representation supplies it. `exists_uniform_bound` of
`Plaplacian.IterFDeriv` bounds `‖iteratedFDeriv ℝ 3 φ y‖` uniformly over a
closed ball, and `ContinuousMultilinearMap.le_opNorm` gives

  `|iteratedFDeriv ℝ 3 φ y (z,z,z)| ≤ ‖iteratedFDeriv ℝ 3 φ y‖ ‖z‖³`,

which is cubic in `z` with a constant independent of it. This is the
representation the curried tower cannot express, and the reason
Finding on the two representations matters in practice.
-/


/-- The trilinear evaluation of the third derivative, bounded. -/
theorem iteratedFDeriv_three_le {φ : EuclSpace d → ℝ} (_hφ : ContDiff ℝ 3 φ)
    {C : ℝ} {y : EuclSpace d} (hC : ‖iteratedFDeriv ℝ 3 φ y‖ ≤ C)
    (z : EuclSpace d) :
    |iteratedFDeriv ℝ 3 φ y (fun _ => z)| ≤ C * ‖z‖ ^ 3 := by
  have h := (iteratedFDeriv ℝ 3 φ y).le_opNorm (fun _ : Fin 3 => z)
  have hprod : ∏ _i : Fin 3, ‖z‖ = ‖z‖ ^ 3 := by
    simp [Finset.prod_const]
  rw [hprod] at h
  have hznn : (0:ℝ) ≤ ‖z‖ ^ 3 := by positivity
  simp only [Real.norm_eq_abs] at h
  nlinarith [h, hC, hznn]

/-- **A uniform cubic bound on the third derivative over a ball.** -/
theorem exists_cubic_bound {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x : EuclSpace d) (ε : ℝ) :
    ∃ C : ℝ, ∀ y ∈ closedBall x ε, ∀ z : EuclSpace d,
      |iteratedFDeriv ℝ 3 φ y (fun _ => z)| ≤ C * ‖z‖ ^ 3 := by
  obtain ⟨C, hC⟩ := exists_uniform_bound hφ x ε
  exact ⟨C, fun y hy z => iteratedFDeriv_three_le hφ (hC y hy) z⟩

end

end PLaplacian
