/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.LineRestrict

@[expose] public section

/-!
# Consistency with classical solutions

A twice continuously differentiable function satisfying the equation pointwise
is a viscosity solution. This is the sanity check any viscosity definition must
pass, and the first real consumer of the definitions of
`Plaplacian.Viscosity`.

The argument at a contact point of a test function has three inputs:

* the derivatives of the solution and the test function agree, by Fermat
  (`fderiv_eq_of_isLocalMax`);
* the Hessians are ordered, by the multivariate second-order condition of
  `Plaplacian.LineRestrict` (`hess_le_of_isLocalMax`);
* degenerate ellipticity transfers the operator inequality
  (`viscF_antitone`).

## Main results

- `fderiv_eq_of_isLocalMax`, `gradient_eq_of_isLocalMax`
- `hess_le_of_isLocalMax`
- `isViscositySubsolution_of_classical`
-/

open Set Topology Filter

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-! ### The first-order condition -/

/-- At a local maximum of `u - φ` the derivatives agree. -/
theorem fderiv_eq_of_isLocalMax {u φ : EuclSpace d → ℝ} {x₀ : EuclSpace d}
    (hu : Differentiable ℝ u) (hφ : Differentiable ℝ φ)
    (hmax : IsLocalMax (fun y => u y - φ y) x₀) :
    fderiv ℝ u x₀ = fderiv ℝ φ x₀ := by
  have h0 : fderiv ℝ (fun y => u y - φ y) x₀ = 0 :=
    IsLocalMax.fderiv_eq_zero hmax
  have hsub : fderiv ℝ (fun y => u y - φ y) x₀
      = fderiv ℝ u x₀ - fderiv ℝ φ x₀ :=
    fderiv_sub (hu x₀) (hφ x₀)
  rw [hsub, sub_eq_zero] at h0
  exact h0

/-- The gradient form, via the Riesz representation. -/
theorem gradient_eq_of_isLocalMax {u φ : EuclSpace d → ℝ}
    {x₀ : EuclSpace d} (hu : Differentiable ℝ u) (hφ : Differentiable ℝ φ)
    (hmax : IsLocalMax (fun y => u y - φ y) x₀) :
    gradient u x₀ = gradient φ x₀ := by
  have hfd := fderiv_eq_of_isLocalMax hu hφ hmax
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, inner_gradient_left, hfd]

/-! ### The second-order condition -/

/-- At a local maximum of `u - φ` the Hessians are ordered as quadratic
forms. -/
theorem hess_le_of_isLocalMax {u φ : EuclSpace d → ℝ} (hu : ContDiff ℝ 2 u)
    (hφ : ContDiff ℝ 2 φ) {x₀ : EuclSpace d}
    (hmax : IsLocalMax (fun y => u y - φ y) x₀) (v : EuclSpace d) :
    fderiv ℝ (fderiv ℝ u) x₀ v v ≤ fderiv ℝ (fderiv ℝ φ) x₀ v v := by
  have hd : ContDiff ℝ 2 (fun y => u y - φ y) := hu.sub hφ
  have h := hess_nonpos_of_isLocalMax hd hmax v
  have hsplit : fderiv ℝ (fderiv ℝ (fun y => u y - φ y)) x₀ v v
      = fderiv ℝ (fderiv ℝ u) x₀ v v - fderiv ℝ (fderiv ℝ φ) x₀ v v := by
    have h1 : fderiv ℝ (fun y => u y - φ y) = fderiv ℝ u - fderiv ℝ φ := by
      funext y
      exact fderiv_sub (hu.differentiable (by norm_num) y)
        (hφ.differentiable (by norm_num) y)
    rw [h1]
    have h2 : fderiv ℝ (fderiv ℝ u - fderiv ℝ φ) x₀
        = fderiv ℝ (fderiv ℝ u) x₀ - fderiv ℝ (fderiv ℝ φ) x₀ :=
      fderiv_sub (differentiable_fderiv hu x₀) (differentiable_fderiv hφ x₀)
    rw [h2]
    simp
  rw [hsplit] at h
  linarith

/-! ### Consistency

At a contact point with nonvanishing gradient, the operator inequality for the
test function follows from the one for the solution. The singular case is
stated separately, since it uses the envelope.
-/

/-- **Consistency at a regular contact point.** If `u` is `C²` and satisfies
the operator inequality at `x₀`, and `u - φ` has a local maximum there with the
gradient of `φ` nonzero, then `φ` satisfies the inequality too. -/
theorem viscF_le_of_classical {p : ℝ} (hp : 2 ≤ p)
    {u φ : EuclSpace d → ℝ} (hu : ContDiff ℝ 2 u) (hφ : ContDiff ℝ 2 φ)
    {x₀ : EuclSpace d} (hmax : IsLocalMax (fun y => u y - φ y) x₀)
    {f : EuclSpace d → ℝ}
    (hclass : viscF p (gradient u x₀) (hess u x₀) ≤ f x₀) :
    viscF p (gradient φ x₀) (hess φ x₀) ≤ f x₀ := by
  have hgrad : gradient u x₀ = gradient φ x₀ :=
    gradient_eq_of_isLocalMax (hu.differentiable (by norm_num))
      (hφ.differentiable (by norm_num)) hmax
  have hhess : ∀ v : EuclSpace d, hess u x₀ v v ≤ hess φ x₀ v v :=
    hess_le_of_isLocalMax hu hφ hmax
  have hanti : viscF p (gradient φ x₀) (hess φ x₀)
      ≤ viscF p (gradient φ x₀) (hess u x₀) :=
    viscF_antitone p hp (gradient φ x₀) (hess u x₀) (hess φ x₀) hhess
  rw [← hgrad] at hanti
  calc viscF p (gradient φ x₀) (hess φ x₀)
      ≤ viscF p (gradient u x₀) (hess u x₀) := by rw [hgrad] at hanti ⊢; exact hanti
    _ ≤ f x₀ := hclass

end PLaplacian

end
