/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Plaplacian.Operator
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Viscosity solutions of the normalized p-Laplace equation

The sub- and supersolution predicates for `- Delta^N_p u = f`, and the
treatment of the singular set on which the operator is undefined.

## The singular set has a closed-form envelope

The operator is undefined where the gradient vanishes, and one might expect a
general construction of the semicontinuous envelopes `F^*` and `F_*` to be
needed --- with the attendant difficulty that the reals are not a complete
lattice, so the `liminf` characterisation of semicontinuity is unavailable.

No such construction is required. For `p >= 2` the envelopes have a closed
form. As `q -> 0` the quantity `<X nu, nu>` with `nu = q / |q|` ranges over
the whole interval between the extreme eigenvalues of `X`, so

  `F_* (0, X) = - laplacianOf X - (p - 2) * lamMax X`,
  `F^* (0, X) = - laplacianOf X - (p - 2) * lamMin X`,

where `lamMax` and `lamMin` are the supremum and infimum of the quadratic form
over the unit sphere. These are `viscFLower` and `viscFUpper` below. The
resulting definition agrees with the one standard in the literature on the
normalized operator, which states the singular case explicitly in terms of
`lambda_max` and `lambda_min` rather than through an abstract envelope.

## The gradient is a vector, not a functional

`fderiv` produces a continuous linear functional, while the operator of
`Plaplacian.Operator` takes a gradient vector. The two are related by the
Riesz representation, and Mathlib's `gradient` is exactly the representative,
with `inner_gradient_left` connecting them. The definitions below use
`gradient`.

## Regular and singular cases are separate fields

Each predicate has the regular and singular conditions as distinct structure
fields rather than a conjunction inside one field. This follows the Mathlib
convention against conjunctive hypotheses: each case is separately applicable,
which matters when using the predicate rather than proving it.

## Main definitions

- `lamMax`, `lamMin`: the extreme eigenvalues as sup and inf over the unit
  sphere.
- `viscFLower`, `viscFUpper`: the envelopes at the singular set.
- `hess`: the Hessian as a continuous bilinear map.
- `IsViscositySubsolution`, `IsViscositySupersolution`,
  `IsViscositySolution`.

## TODO

The stability API: consistency with classical solutions; stability under
addition of a smooth function; the supremum of subsolutions; restriction to a
subdomain. These are what a convergence proof consumes, and none is yet
proved.
-/

open Metric Set

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-! ### The extreme eigenvalues -/

/-- The largest eigenvalue of a bilinear form, as the supremum of the
quadratic form over the unit sphere. -/
def lamMax (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) : ℝ :=
  sSup ((fun v : EuclSpace d => X v v) '' {v | ‖v‖ = 1})

/-- The smallest eigenvalue. -/
def lamMin (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) : ℝ :=
  sInf ((fun v : EuclSpace d => X v v) '' {v | ‖v‖ = 1})

/-- The unit sphere is nonempty in dimension at least one. -/
lemma nonempty_unitSphere (hd : 0 < d) :
    {v : EuclSpace d | ‖v‖ = 1}.Nonempty :=
  ⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ), by simp⟩

/-- The quadratic form is bounded on the unit sphere by the operator norm, so
`lamMax` is not a junk value. -/
lemma bddAbove_quadratic (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) :
    BddAbove ((fun v : EuclSpace d => X v v) '' {v | ‖v‖ = 1}) := by
  refine ⟨‖X‖, ?_⟩
  rintro a ⟨v, hv, rfl⟩
  have h1 : ‖X v v‖ ≤ ‖X v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
  have h2 : ‖X v‖ ≤ ‖X‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
  have hv1 : ‖v‖ = 1 := hv
  rw [hv1] at h1 h2
  simp only [Real.norm_eq_abs] at h1
  have := le_abs_self (X v v)
  nlinarith [h1, h2, norm_nonneg (X v)]

/-- The infinity Laplacian in any direction is below the largest eigenvalue.
This is what identifies `lamMax` as an envelope value. -/
lemma infLaplacianOf_le_lamMax {q : EuclSpace d} (hq : q ≠ 0)
    (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) :
    infLaplacianOf q X ≤ lamMax X := by
  unfold infLaplacianOf lamMax
  have hqn : (0 : ℝ) < ‖q‖ := norm_pos_iff.2 hq
  have hunit : ‖(‖q‖⁻¹ • q)‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  exact le_csSup (bddAbove_quadratic X) ⟨‖q‖⁻¹ • q, hunit, rfl⟩

/-! ### The envelopes -/

/-- The lower envelope at a singular point; used for subsolutions. -/
def viscFLower (p : ℝ) (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) : ℝ :=
  - laplacianOf X - (p - 2) * lamMax X

/-- The upper envelope at a singular point; used for supersolutions. -/
def viscFUpper (p : ℝ) (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) : ℝ :=
  - laplacianOf X - (p - 2) * lamMin X

/-- **Consistency of the lower envelope**: it does not exceed the operator.
This is what makes the singular case a relaxation rather than an arbitrary
choice. -/
theorem viscFLower_le (p : ℝ) (hp : 2 ≤ p) (q : EuclSpace d)
    (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ)
    (hub : infLaplacianOf q X ≤ lamMax X) :
    viscFLower p X ≤ viscF p q X := by
  unfold viscFLower viscF normPLapOf
  nlinarith [hub]

/-! ### The predicates -/

/-- The Hessian of a test function, as a continuous bilinear map. An `abbrev`
so that `fderiv` lemmas apply without unfolding. -/
abbrev hess (φ : EuclSpace d → ℝ) (x : EuclSpace d) :
    EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ φ) x

/-- **Viscosity subsolution of `- Delta^N_p u = f`.** -/
structure IsViscositySubsolution (p : ℝ) (Ω : Set (EuclSpace d))
    (f : EuclSpace d → ℝ) (u : EuclSpace d → ℝ) : Prop where
  usc : UpperSemicontinuousOn u Ω
  regular : ∀ (φ : EuclSpace d → ℝ), ContDiff ℝ 2 φ →
    ∀ x₀ ∈ Ω, IsLocalMax (fun y => u y - φ y) x₀ →
      gradient φ x₀ ≠ 0 →
      viscF p (gradient φ x₀) (hess φ x₀) ≤ f x₀
  singular : ∀ (φ : EuclSpace d → ℝ), ContDiff ℝ 2 φ →
    ∀ x₀ ∈ Ω, IsLocalMax (fun y => u y - φ y) x₀ →
      gradient φ x₀ = 0 →
      viscFLower p (hess φ x₀) ≤ f x₀

/-- **Viscosity supersolution.** -/
structure IsViscositySupersolution (p : ℝ) (Ω : Set (EuclSpace d))
    (f : EuclSpace d → ℝ) (u : EuclSpace d → ℝ) : Prop where
  lsc : LowerSemicontinuousOn u Ω
  regular : ∀ (φ : EuclSpace d → ℝ), ContDiff ℝ 2 φ →
    ∀ x₀ ∈ Ω, IsLocalMin (fun y => u y - φ y) x₀ →
      gradient φ x₀ ≠ 0 →
      f x₀ ≤ viscF p (gradient φ x₀) (hess φ x₀)
  singular : ∀ (φ : EuclSpace d → ℝ), ContDiff ℝ 2 φ →
    ∀ x₀ ∈ Ω, IsLocalMin (fun y => u y - φ y) x₀ →
      gradient φ x₀ = 0 →
      f x₀ ≤ viscFUpper p (hess φ x₀)

/-- **Viscosity solution.** -/
structure IsViscositySolution (p : ℝ) (Ω : Set (EuclSpace d))
    (f : EuclSpace d → ℝ) (u : EuclSpace d → ℝ) : Prop where
  sub : IsViscositySubsolution p Ω f u
  super : IsViscositySupersolution p Ω f u

/-- A solution is semicontinuous from both sides on the domain. -/
theorem IsViscositySolution.semicontinuous {p : ℝ} {Ω : Set (EuclSpace d)}
    {f u : EuclSpace d → ℝ} (h : IsViscositySolution p Ω f u) :
    UpperSemicontinuousOn u Ω ∧ LowerSemicontinuousOn u Ω :=
  ⟨h.sub.usc, h.super.lsc⟩

end PLaplacian

end
