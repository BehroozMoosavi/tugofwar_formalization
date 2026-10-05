/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.SingularCase

/-!
# The quartic perturbation

Adding the fourth power of the distance to the base point turns a maximum of
the difference into a strict one, the quartic vanishing at the base point and
being positive elsewhere. Its gradient and Hessian vanish at the base point, so
adding it changes nothing the convergence theorems see.

The gradient vanishes because the quartic has a minimum there. For the
Hessian, the quartic is the square of the squared distance, so its derivative
is a scalar factor times the derivative of the squared distance; both factors
vanish at the base point, and so does the value of the product rule there.

## Main results

- quartS, quart, contDiff_quart
- quart_self, quart_pos, quart_nonneg
- fderiv_quart_self, hess_quart_self
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The quartic perturbation

Adding `q w = ‖w - x₀‖⁴` to a test function turns a maximum of the difference
into a strict one, since `q` vanishes at `x₀` and is positive elsewhere. For
this to change nothing the convergence theorems see, `q` must have vanishing
gradient and Hessian at `x₀`.

The gradient vanishes because `q` has a minimum there. For the Hessian, write
`q = s²` with `s w = ‖w - x₀‖²`, so that `Dq = c • Ds` with `c = 2 s`. Both
factors vanish at `x₀` --- `c` because `s` does, `Ds` because `s` has a
minimum --- so the product rule's value at `x₀`, which is
`c x₀ • L' + c'.smulRight (Ds x₀)`, is zero.
-/

/-- The squared distance to the base point. -/
def quartS (x₀ : EuclSpace d) : EuclSpace d → ℝ := fun w => ‖w - x₀‖ ^ 2

/-- The quartic perturbation. -/
def quart (x₀ : EuclSpace d) : EuclSpace d → ℝ := fun w => (‖w - x₀‖ ^ 2) ^ 2

theorem contDiff_quartS (x₀ : EuclSpace d) {n : WithTop ℕ∞} :
    ContDiff ℝ n (quartS x₀) := by
  unfold quartS
  exact (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)

theorem contDiff_quart (x₀ : EuclSpace d) {n : WithTop ℕ∞} :
    ContDiff ℝ n (quart x₀) := by
  have h : quart x₀ = fun w => quartS x₀ w ^ 2 := rfl
  rw [h]
  exact (contDiff_quartS x₀).pow 2

theorem quart_self (x₀ : EuclSpace d) : quart x₀ x₀ = 0 := by
  simp [quart]

theorem quart_pos {x₀ w : EuclSpace d} (hw : w ≠ x₀) : 0 < quart x₀ w := by
  unfold quart
  have : 0 < ‖w - x₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hw)
  positivity

theorem quart_nonneg (x₀ w : EuclSpace d) : 0 ≤ quart x₀ w := by
  unfold quart; positivity

/-- The squared distance has a minimum at the base point, so its derivative
there vanishes. -/
theorem fderiv_quartS_self (x₀ : EuclSpace d) :
    fderiv ℝ (quartS x₀) x₀ = 0 := by
  apply IsLocalMin.fderiv_eq_zero
  refine Filter.Eventually.of_forall (fun w => ?_)
  unfold quartS
  simp

/-- The derivative of the quartic, as twice the squared distance times the
derivative of the squared distance. -/
theorem fderiv_quart_eq (x₀ w : EuclSpace d) :
    fderiv ℝ (quart x₀) w = (2 * quartS x₀ w) • fderiv ℝ (quartS x₀) w := by
  have hd : HasFDerivAt (quartS x₀) (fderiv ℝ (quartS x₀) w) w :=
    ((contDiff_quartS x₀ (n := 1)).differentiable (by norm_num) w).hasFDerivAt
  have h := hd.pow 2
  have hq : quart x₀ = fun x => quartS x₀ x ^ 2 := rfl
  rw [hq, h.fderiv]
  congr 1
  simp

/-- **The gradient of the quartic vanishes at the base point.** -/
theorem fderiv_quart_self (x₀ : EuclSpace d) :
    fderiv ℝ (quart x₀) x₀ = 0 := by
  rw [fderiv_quart_eq, fderiv_quartS_self, smul_zero]

/-- **The Hessian of the quartic vanishes at the base point.** -/
theorem hess_quart_self (x₀ : EuclSpace d) :
    fderiv ℝ (fderiv ℝ (quart x₀)) x₀ = 0 := by
  have heq : fderiv ℝ (quart x₀)
      = (fun w => 2 * quartS x₀ w) • fderiv ℝ (quartS x₀) := by
    funext w; exact fderiv_quart_eq x₀ w
  rw [heq]
  -- the scalar factor
  have hcd : Differentiable ℝ (fun w => 2 * quartS x₀ w) :=
    ((contDiff_quartS x₀ (n := 1)).differentiable (by norm_num)).const_mul 2
  have hc := (hcd x₀).hasFDerivAt
  -- the derivative factor
  have hLd : Differentiable ℝ (fderiv ℝ (quartS x₀)) :=
    ((contDiff_quartS x₀ (n := 2)).fderiv_right (m := 1)
      (by norm_num)).differentiable (by norm_num)
  have hL := (hLd x₀).hasFDerivAt
  -- the product rule, with both factors vanishing at the base point
  have h := hc.smul hL
  have hs0 : quartS x₀ x₀ = 0 := by simp [quartS]
  have hval : (2 * quartS x₀ x₀) • fderiv ℝ (fderiv ℝ (quartS x₀)) x₀
      + (fderiv ℝ (fun w => 2 * quartS x₀ w) x₀).smulRight
          (fderiv ℝ (quartS x₀) x₀) = 0 := by
    rw [fderiv_quartS_self, hs0]
    ext v w
    simp
  rw [hval] at h
  exact h.fderiv

end

end PLaplacian
