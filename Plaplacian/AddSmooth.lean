/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.MaxSub

/-!
# Stability under adding a smooth function

Testing `u + psi` against `phi` is the same as testing `u` against
`phi - psi`, so the subsolution property of `u` gives the operator inequality
for `phi - psi`.

It cannot be converted into an inequality for `phi` alone, because the
operator is not additive in either the gradient or the Hessian. This is the
third appearance of that non-additivity: it first blocked the perturbation
route to the comparison principle in the discrete theory, then explained why
the quantitative gap for the concave perturbation could not be used, and now
determines the form of this statement. The version proved here is the honest
one, and also the usable one, since a convergence proof applies the
subsolution property to a perturbed test function and needs exactly this.

## Main results

- `gradient_sub`, `hess_sub`: derivatives of a difference.
- `isLocalMax_shift`: shifting the function is shifting the test function.
- `IsViscositySubsolution.add_smooth`
-/

open Set Topology Filter

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## Adding a smooth function

Testing `u + ψ` against `φ` is the same as testing `u` against `φ - ψ`, so the
subsolution property of `u` gives the operator inequality for `φ - ψ`. Since
`F` is not additive in either the gradient or the Hessian, this cannot be
converted into an inequality for `φ` alone, and the statement below is the
honest form. It is also the usable form: a convergence proof applies the
subsolution property to a perturbed test function and needs exactly this.
-/

/-- The gradient of a difference. -/
theorem gradient_sub {u v : EuclSpace d → ℝ} (hu : Differentiable ℝ u)
    (hv : Differentiable ℝ v) (x : EuclSpace d) :
    gradient (fun y => u y - v y) x = gradient u x - gradient v x := by
  refine ext_inner_right ℝ fun w => ?_
  rw [inner_gradient_left, inner_sub_left, inner_gradient_left,
      inner_gradient_left]
  have heq : (fun y => u y - v y) = u - v := rfl
  rw [heq, fderiv_sub (hu x) (hv x)]
  simp

/-- The Hessian of a difference. -/
theorem hess_sub {u v : EuclSpace d → ℝ} (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v) (x : EuclSpace d) :
    hess (fun y => u y - v y) x = hess u x - hess v x := by
  unfold hess
  have h1 : fderiv ℝ (fun y => u y - v y) = fderiv ℝ u - fderiv ℝ v := by
    funext y
    exact fderiv_sub (hu.differentiable (by norm_num) y)
      (hv.differentiable (by norm_num) y)
  rw [h1]
  exact fderiv_sub (differentiable_fderiv hu x) (differentiable_fderiv hv x)

/-- Testing `u + ψ` against `φ` is testing `u` against `φ - ψ`. -/
theorem isLocalMax_shift {u ψ φ : EuclSpace d → ℝ} {x₀ : EuclSpace d}
    (hmax : IsLocalMax (fun y => (u y + ψ y) - φ y) x₀) :
    IsLocalMax (fun y => u y - (fun z => φ z - ψ z) y) x₀ := by
  have heq : (fun y => u y - (fun z => φ z - ψ z) y)
      = fun y => (u y + ψ y) - φ y := by
    funext y; ring
  rw [heq]
  exact hmax

/-- **Stability under adding a smooth function.** -/
theorem IsViscositySubsolution.add_smooth {p : ℝ} {Ω : Set (EuclSpace d)}
    {f u : EuclSpace d → ℝ} (h : IsViscositySubsolution p Ω f u)
    {ψ : EuclSpace d → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (φ : EuclSpace d → ℝ) (hφ : ContDiff ℝ 2 φ)
    {x₀ : EuclSpace d} (hx₀ : x₀ ∈ Ω)
    (hmax : IsLocalMax (fun y => (u y + ψ y) - φ y) x₀)
    (hgrad : gradient φ x₀ - gradient ψ x₀ ≠ 0) :
    viscF p (gradient φ x₀ - gradient ψ x₀)
      (hess φ x₀ - hess ψ x₀) ≤ f x₀ := by
  have hdiff : ContDiff ℝ 2 (fun z => φ z - ψ z) := hφ.sub hψ
  have hg : gradient (fun z => φ z - ψ z) x₀
      = gradient φ x₀ - gradient ψ x₀ :=
    gradient_sub (hφ.differentiable (by norm_num))
      (hψ.differentiable (by norm_num)) x₀
  have hh : hess (fun z => φ z - ψ z) x₀ = hess φ x₀ - hess ψ x₀ :=
    hess_sub hφ hψ x₀
  have hgrad' : gradient (fun z => φ z - ψ z) x₀ ≠ 0 := by rwa [hg]
  have hres := h.regular (fun z => φ z - ψ z) hdiff x₀ hx₀
    (isLocalMax_shift hmax) hgrad'
  rwa [hg, hh] at hres

end

end PLaplacian
