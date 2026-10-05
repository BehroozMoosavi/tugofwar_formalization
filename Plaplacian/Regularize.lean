/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Quartic

/-!
# Regularizing the test function

A general C three test function at a local maximum is brought to the form the
convergence theorems want --- bounded, at a strict maximum --- by adding the
quartic perturbation and multiplying by a smooth bump equal to one on a closed
ball about the base point. The quartic makes the maximum strict; the bump
makes the function bounded, having compact support; and since the result
agrees with the perturbed function near the base point, its gradient and
Hessian there are those of the original, the quartic contributing nothing.

The operator locality is what makes the cut-off harmless: only values near the
base point enter, so changing the test function far away changes nothing.

The statement is for a generic function in place of the upper relaxed limit,
so that it serves the supersolution through the negated family.

## Main results

- regularize
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # Regularizing the test function

The convergence theorems want a bounded test function at a strict maximum. A
general test function at a local maximum is brought to that form by

  `ψ = χ · (φ + q)`,

with `q` the quartic perturbation and `χ` a smooth bump equal to one on a
closed ball about the base point. The quartic makes the maximum strict; the
bump makes the test function bounded, having compact support; and because `ψ`
agrees with `φ + q` near the base point, its gradient and Hessian there are
those of `φ + q`, which are those of `φ`, the quartic contributing nothing.

The statement is for a generic function `V` in place of the upper relaxed
limit, so that the same lemma serves the supersolution through the upper limit
of the negated family.
-/


/-- **Regularization.** From a local maximum of `V - φ`, a bounded `C³` test
function with a strict maximum of `V - ψ` on a closed ball, agreeing with `φ`
to second order at the base point. -/
theorem regularize {V φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    {x₀ : EuclSpace d} (hmax : IsLocalMax (fun w => V w - φ w) x₀)
    {R : ℝ} (hR : 0 < R) :
    ∃ ψ : EuclSpace d → ℝ, ∃ r : ℝ, 0 < r ∧ r ≤ R ∧
      ContDiff ℝ 3 ψ ∧ BddMeas ψ ∧ (∃ B, ∀ y, |ψ y| ≤ B) ∧
      IsStrictMaxOn (fun w => V w - ψ w) x₀ r ∧
      gradient ψ x₀ = gradient φ x₀ ∧
      fderiv ℝ (fderiv ℝ ψ) x₀ = fderiv ℝ (fderiv ℝ φ) x₀ := by
  -- the bump, the perturbed function, and the cut-off one
  let χ : ContDiffBump x₀ := ⟨R, 2 * R, hR, by linarith⟩
  set ψ0 : EuclSpace d → ℝ := fun w => φ w + quart x₀ w with hψ0def
  set ψ : EuclSpace d → ℝ := fun w => χ w * ψ0 w with hψdef
  have hψ0 : ContDiff ℝ 3 ψ0 := hφ.add (contDiff_quart x₀)
  have hψ : ContDiff ℝ 3 ψ := (χ.contDiff (n := 3)).mul hψ0
  -- the cut-off function agrees with the perturbed one on the inner ball
  have hagree : ∀ w ∈ closedBall x₀ R, ψ w = ψ0 w := by
    intro w hw
    have h1 : χ w = 1 := χ.one_of_mem_closedBall hw
    simp only [hψdef, h1, one_mul]
  have hev : ψ =ᶠ[𝓝 x₀] ψ0 := by
    filter_upwards [closedBall_mem_nhds x₀ hR] with w hw
    exact hagree w hw
  -- so their derivatives agree at the base point
  have hd1 : fderiv ℝ ψ x₀ = fderiv ℝ ψ0 x₀ := hev.fderiv_eq
  have hd2 : fderiv ℝ (fderiv ℝ ψ) x₀ = fderiv ℝ (fderiv ℝ ψ0) x₀ :=
    hev.fderiv.fderiv_eq
  -- and the perturbed function has the derivatives of the original
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hqd : Differentiable ℝ (quart x₀) :=
    (contDiff_quart x₀ (n := 1)).differentiable (by norm_num)
  have hψ0d1 : fderiv ℝ ψ0 = fun w => fderiv ℝ φ w + fderiv ℝ (quart x₀) w := by
    funext w; exact fderiv_add (hφd w) (hqd w)
  have hfx : fderiv ℝ ψ0 x₀ = fderiv ℝ φ x₀ := by
    rw [hψ0d1]; simp only [fderiv_quart_self, add_zero]
  have hhx : fderiv ℝ (fderiv ℝ ψ0) x₀ = fderiv ℝ (fderiv ℝ φ) x₀ := by
    rw [hψ0d1]
    have hφd2 : Differentiable ℝ (fderiv ℝ φ) :=
      (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
    have hqd2 : Differentiable ℝ (fderiv ℝ (quart x₀)) :=
      ((contDiff_quart x₀ (n := 2)).fderiv_right (m := 1)
        (by norm_num)).differentiable (by norm_num)
    rw [show (fun w => fderiv ℝ φ w + fderiv ℝ (quart x₀) w)
        = fderiv ℝ φ + fderiv ℝ (quart x₀) from rfl,
      fderiv_add (hφd2 x₀) (hqd2 x₀), hess_quart_self, add_zero]
  have hgrad : gradient ψ x₀ = gradient φ x₀ := by
    unfold gradient; rw [hd1, hfx]
  -- boundedness, from compact support
  have hcs : HasCompactSupport ψ := χ.hasCompactSupport.mul_right
  obtain ⟨B, hB⟩ := hψ.continuous.bounded_above_of_compact_support hcs
  have hbd : ∀ y, |ψ y| ≤ B := fun y => by
    rw [← Real.norm_eq_abs]; exact hB y
  have hbm : BddMeas ψ := ⟨hψ.continuous.measurable, ⟨B, hbd⟩⟩
  -- the strict maximum
  obtain ⟨ρ, hρ, hloc⟩ := exists_radius_of_isLocalMax hmax
  set r := min (ρ / 2) R with hrdef
  have hr : 0 < r := lt_min (by linarith) hR
  have hrR : r ≤ R := min_le_right _ _
  refine ⟨ψ, r, hr, hrR, hψ, hbm, ⟨B, hbd⟩, ?_, hgrad, by rw [hd2, hhx]⟩
  intro w hw hne
  have hwR : w ∈ closedBall x₀ R := closedBall_subset_closedBall hrR hw
  have hwρ : w ∈ ball x₀ ρ := by
    rw [mem_ball]
    rw [mem_closedBall] at hw
    have := min_le_left (ρ / 2) R
    linarith
  have hψw : ψ w = φ w + quart x₀ w := hagree w hwR
  have hψx : ψ x₀ = φ x₀ := by
    rw [hagree x₀ (mem_closedBall_self hR.le)]
    simp only [hψ0def, quart_self, add_zero]
  have hlw := hloc w hwρ
  have hqp := quart_pos hne
  show V w - ψ w < V x₀ - ψ x₀
  rw [hψw, hψx]
  linarith

end

end PLaplacian
