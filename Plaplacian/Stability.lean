/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Consistency

@[expose] public section

/-!
# Stability of the viscosity notions

Two stability properties, both consumed by a convergence proof.

**Restriction.** The test condition is local, so a subsolution on a domain
restricts to a subsolution on any subset. The proof is three lines of field
plumbing, which is the payoff for having made the regular and singular
conditions separate structure fields in `Plaplacian.Viscosity` rather than a
conjunction inside one field.

**Adding a constant.** The operator is one-homogeneous with no zeroth-order
term, so it sees only the gradient and the Hessian. Both are unaffected by
adding a constant to the solution, so `u + c` solves the same equation. This
is the cheapest genuine stability statement and a good check that the
definitions are usable in practice rather than merely well formed.

A note on technique: `IsLocalMax` is a filter statement, and after it has been
unfolded anywhere in a proof, dot notation stops working on it. The reliable
way to use it is `filter_upwards [hmax] with y hy`, which needs neither dot
notation nor a named lemma. Mathlib has no `IsLocalMax.add_const`.

## Main results

- `IsViscositySubsolution.mono`, `IsViscositySupersolution.mono`,
  `IsViscositySolution.mono`
- `gradient_add_const`
- `IsViscositySubsolution.add_const`
-/

open Set Topology Filter

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-! ### Restriction to a subdomain -/

theorem IsViscositySubsolution.mono {p : ℝ} {Ω Ω' : Set (EuclSpace d)}
    {f u : EuclSpace d → ℝ} (h : IsViscositySubsolution p Ω f u)
    (hsub : Ω' ⊆ Ω) :
    IsViscositySubsolution p Ω' f u where
  usc := h.usc.mono hsub
  regular := fun φ hφ x₀ hx₀ hmax hgrad =>
    h.regular φ hφ x₀ (hsub hx₀) hmax hgrad
  singular := fun φ hφ x₀ hx₀ hmax hgrad =>
    h.singular φ hφ x₀ (hsub hx₀) hmax hgrad

theorem IsViscositySupersolution.mono {p : ℝ} {Ω Ω' : Set (EuclSpace d)}
    {f u : EuclSpace d → ℝ} (h : IsViscositySupersolution p Ω f u)
    (hsub : Ω' ⊆ Ω) :
    IsViscositySupersolution p Ω' f u where
  lsc := h.lsc.mono hsub
  regular := fun φ hφ x₀ hx₀ hmin hgrad =>
    h.regular φ hφ x₀ (hsub hx₀) hmin hgrad
  singular := fun φ hφ x₀ hx₀ hmin hgrad =>
    h.singular φ hφ x₀ (hsub hx₀) hmin hgrad

theorem IsViscositySolution.mono {p : ℝ} {Ω Ω' : Set (EuclSpace d)}
    {f u : EuclSpace d → ℝ} (h : IsViscositySolution p Ω f u)
    (hsub : Ω' ⊆ Ω) :
    IsViscositySolution p Ω' f u where
  sub := h.sub.mono hsub
  super := h.super.mono hsub

/-! ### Adding a constant -/

/-- The gradient is unchanged by adding a constant. Mathlib has
`fderiv_add_const` but not the gradient form. -/
theorem gradient_add_const (φ : EuclSpace d → ℝ) (c : ℝ) (x : EuclSpace d) :
    gradient (fun y => φ y + c) x = gradient φ x := by
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_gradient_left, inner_gradient_left, fderiv_add_const]

/-- Adding a constant preserves a local maximum of a difference. -/
theorem isLocalMax_add_const {u φ : EuclSpace d → ℝ} (c : ℝ)
    {x₀ : EuclSpace d} (hmax : IsLocalMax (fun y => u y - φ y) x₀) :
    IsLocalMax (fun y => (u y + c) - φ y) x₀ := by
  have heq : (fun y => (u y + c) - φ y) = fun y => (u y - φ y) + c := by
    funext y; ring
  rw [heq]
  filter_upwards [hmax] with y hy
  linarith [hy]

/-- Semicontinuity is preserved by adding a constant. -/
theorem upperSemicontinuousOn_add_const {u : EuclSpace d → ℝ}
    {Ω : Set (EuclSpace d)} (h : UpperSemicontinuousOn u Ω) (c : ℝ) :
    UpperSemicontinuousOn (fun y => u y + c) Ω := by
  intro x hx y hy
  have := h x hx (y - c) (by linarith)
  filter_upwards [this] with z hz
  linarith

/-- The Hessian is unchanged by adding a constant. -/
theorem hess_add_const (φ : EuclSpace d → ℝ) (c : ℝ) :
    hess (fun y => φ y + c) = hess φ := by
  funext x
  unfold hess
  have h1 : fderiv ℝ (fun y => φ y + c) = fderiv ℝ φ := by
    funext y
    exact fderiv_add_const c
  rw [h1]

/-- **Adding a constant preserves subsolutions.** The operator sees only the
gradient and the Hessian, both unchanged. -/
theorem IsViscositySubsolution.add_const {p : ℝ} {Ω : Set (EuclSpace d)}
    {f u : EuclSpace d → ℝ} (h : IsViscositySubsolution p Ω f u) (c : ℝ) :
    IsViscositySubsolution p Ω f (fun y => u y + c) where
  usc := upperSemicontinuousOn_add_const h.usc c
  regular := fun φ hφ x₀ hx₀ hmax hgrad => by
    have hmax' : IsLocalMax (fun y => u y - (fun z => φ z - c) y) x₀ := by
      have heq : (fun y => u y - (fun z => φ z - c) y)
          = fun y => (u y + c) - φ y := by funext y; ring
      rw [heq]
      exact hmax
    have hφ' : ContDiff ℝ 2 (fun z => φ z - c) := hφ.sub contDiff_const
    have hgrad' : gradient (fun z => φ z - c) x₀ ≠ 0 := by
      have : gradient (fun z => φ z - c) x₀ = gradient φ x₀ := by
        have heq : (fun z => φ z - c) = fun z => φ z + (-c) := by
          funext z; ring
        rw [heq, gradient_add_const]
      rwa [this]
    have hg : gradient (fun z => φ z - c) x₀ = gradient φ x₀ := by
      have heq : (fun z => φ z - c) = fun z => φ z + (-c) := by funext z; ring
      rw [heq, gradient_add_const]
    have hh : hess (fun z => φ z - c) x₀ = hess φ x₀ := by
      have heq : (fun z => φ z - c) = fun z => φ z + (-c) := by funext z; ring
      rw [heq, hess_add_const]
    have hres := h.regular (fun z => φ z - c) hφ' x₀ hx₀ hmax' hgrad'
    rwa [hg, hh] at hres
  singular := fun φ hφ x₀ hx₀ hmax hgrad => by
    have hmax' : IsLocalMax (fun y => u y - (fun z => φ z - c) y) x₀ := by
      have heq : (fun y => u y - (fun z => φ z - c) y)
          = fun y => (u y + c) - φ y := by funext y; ring
      rw [heq]; exact hmax
    have hφ' : ContDiff ℝ 2 (fun z => φ z - c) := hφ.sub contDiff_const
    have hg : gradient (fun z => φ z - c) x₀ = gradient φ x₀ := by
      have heq : (fun z => φ z - c) = fun z => φ z + (-c) := by funext z; ring
      rw [heq, gradient_add_const]
    have hh : hess (fun z => φ z - c) x₀ = hess φ x₀ := by
      have heq : (fun z => φ z - c) = fun z => φ z + (-c) := by funext z; ring
      rw [heq, hess_add_const]
    have hgrad' : gradient (fun z => φ z - c) x₀ = 0 := by rwa [hg]
    have hres := h.singular (fun z => φ z - c) hφ' x₀ hx₀ hmax' hgrad'
    rwa [hh] at hres

end PLaplacian

end
