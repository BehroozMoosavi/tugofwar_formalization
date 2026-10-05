/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Regularize

/-!
# The viscosity property, for C three test functions

The upper relaxed limit is a viscosity subsolution and the lower relaxed limit
a viscosity supersolution of the homogeneous normalized p-Laplace equation, in
the sense of the layer-two predicates with test functions of class C three.

Each field follows one pattern: the domain being open, a closed ball about the
point lies inside it; the regularization produces a bounded test function at a
strict maximum agreeing to second order with the given one; the convergence
theorems apply; and the gradient and Hessian at the point are the given ones.
The supersolution is obtained through the negated family, so that only the
subsolution theorems are used.

## Scope

The layer-two predicates test with C two functions. That the two classes of
test function give the same notion is standard in viscosity theory and is not
proved here.

## Main results

- IsViscositySubsolution3, IsViscositySupersolution3
- visc_reg_sub, visc_sing_sub, visc_reg_super, visc_sing_super
- ubar_isViscositySubsolution3, lbar_isViscositySupersolution3
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The viscosity property, for `C³` test functions

The upper relaxed limit is a viscosity subsolution, and the lower one a
supersolution, of the homogeneous equation, in the sense of the layer-two
predicates but with test functions of class `C³` rather than `C²`.

Each field follows the same pattern. The domain being open, a closed ball
about the point lies inside it; `regularize` produces a bounded test function
at a strict maximum, agreeing to second order with the given one; the
convergence theorems apply to it; and its gradient and Hessian at the point are
the given ones.

The supersolution is obtained through the negated family: a local minimum of
the lower limit minus the test function is a local maximum of the upper limit
of the negated family minus the negated test function, so the subsolution
theorems apply and the signs flip.

## Scope

The layer-two predicates test with `C²` functions. The reduction from `C²` to
`C³` --- that the two classes of test function give the same notion --- is
standard in viscosity theory but not proved here.
-/

/-- The subsolution predicate, with test functions of class `C³`. -/
structure IsViscositySubsolution3 (p : ℝ) (Ω : Set (EuclSpace d))
    (f u : EuclSpace d → ℝ) : Prop where
  usc : UpperSemicontinuousOn u Ω
  regular : ∀ φ : EuclSpace d → ℝ, ContDiff ℝ 3 φ → ∀ x₀ ∈ Ω,
    IsLocalMax (fun y => u y - φ y) x₀ → gradient φ x₀ ≠ 0 →
      viscF p (gradient φ x₀) (hess φ x₀) ≤ f x₀
  singular : ∀ φ : EuclSpace d → ℝ, ContDiff ℝ 3 φ → ∀ x₀ ∈ Ω,
    IsLocalMax (fun y => u y - φ y) x₀ → gradient φ x₀ = 0 →
      viscFLower p (hess φ x₀) ≤ f x₀

/-- The supersolution predicate, with test functions of class `C³`. -/
structure IsViscositySupersolution3 (p : ℝ) (Ω : Set (EuclSpace d))
    (f u : EuclSpace d → ℝ) : Prop where
  lsc : LowerSemicontinuousOn u Ω
  regular : ∀ φ : EuclSpace d → ℝ, ContDiff ℝ 3 φ → ∀ x₀ ∈ Ω,
    IsLocalMin (fun y => u y - φ y) x₀ → gradient φ x₀ ≠ 0 →
      f x₀ ≤ viscF p (gradient φ x₀) (hess φ x₀)
  singular : ∀ φ : EuclSpace d → ℝ, ContDiff ℝ 3 φ → ∀ x₀ ∈ Ω,
    IsLocalMin (fun y => u y - φ y) x₀ → gradient φ x₀ = 0 →
      f x₀ ≤ viscFUpper p (hess φ x₀)

/-- An open set contains a closed ball about each of its points. -/
theorem exists_closedBall_subset {Ω : Set (EuclSpace d)} (hΩ : IsOpen Ω)
    {x₀ : EuclSpace d} (hx₀ : x₀ ∈ Ω) :
    ∃ R > 0, closedBall x₀ R ⊆ Ω := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hΩ x₀ hx₀
  exact ⟨ε / 2, by linarith,
    (closedBall_subset_ball (by linarith)).trans hball⟩

/-- A local minimum of the lower limit minus the test function is a local
maximum of the upper limit of the negated family minus the negated test
function. -/
theorem localMax_neg_of_localMin {u : ℝ → EuclSpace d → ℝ}
    {φ : EuclSpace d → ℝ} {x₀ : EuclSpace d}
    (hmin : IsLocalMin (fun y => lbar u y - φ y) x₀) :
    IsLocalMax (fun y => ubar (fun ε y => -u ε y) y - (fun y => -φ y) y) x₀ := by
  unfold IsLocalMin IsMinFilter at hmin
  unfold IsLocalMax IsMaxFilter
  filter_upwards [hmin] with w hw
  have h1 := lbar_eq_neg_ubar_neg u w
  have h2 := lbar_eq_neg_ubar_neg u x₀
  change lbar u x₀ - φ x₀ ≤ lbar u w - φ w at hw
  change ubar (fun ε y => -u ε y) w - -φ w
    ≤ ubar (fun ε y => -u ε y) x₀ - -φ x₀
  linarith

/-- **The regular subsolution field.** -/
theorem visc_reg_sub [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} (hΩ : IsOpen Ω) {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε))
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ) {x₀ : EuclSpace d}
    (hx₀ : x₀ ∈ Ω) (hmax : IsLocalMax (fun y => ubar u y - φ y) x₀)
    (hg : gradient φ x₀ ≠ 0) :
    viscF p (gradient φ x₀) (hess φ x₀) ≤ 0 := by
  obtain ⟨R, hR, hcb⟩ := exists_closedBall_subset hΩ hx₀
  obtain ⟨ψ, r, hr, hrR, hψ, hψb, ⟨B, hB⟩, hstrict, hgrad, hhess⟩ :=
    regularize (V := ubar u) hφ hmax hR
  have hΩr : closedBall x₀ r ⊆ Ω :=
    (closedBall_subset_closedBall hrR).trans hcb
  have hgψ : gradient ψ x₀ ≠ 0 := by rw [hgrad]; exact hg
  have h := regular_subsol hd hp hpd hC hu hψ hψb hB hr hΩr hstrict hgψ
  rw [hgrad, hhess] at h
  exact viscF_le_of_chain h

/-- **The singular subsolution field.** -/
theorem visc_sing_sub [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} (hΩ : IsOpen Ω) {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε))
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ) {x₀ : EuclSpace d}
    (hx₀ : x₀ ∈ Ω) (hmax : IsLocalMax (fun y => ubar u y - φ y) x₀) :
    viscFLower p (hess φ x₀) ≤ 0 := by
  obtain ⟨R, hR, hcb⟩ := exists_closedBall_subset hΩ hx₀
  obtain ⟨ψ, r, hr, hrR, hψ, hψb, ⟨B, hB⟩, hstrict, _hgrad, hhess⟩ :=
    regularize (V := ubar u) hφ hmax hR
  have hΩr : closedBall x₀ r ⊆ Ω :=
    (closedBall_subset_closedBall hrR).trans hcb
  have h := singular_subsol hd hp hpd hC hu hψ hψb hB hr hΩr hstrict
  rw [hess_eq_fderiv, hhess] at h
  rw [hess_eq_fderiv]
  exact h

/-- **The regular supersolution field**, through the negated family. -/
theorem visc_reg_super [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} (hΩ : IsOpen Ω) {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε))
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ) {x₀ : EuclSpace d}
    (hx₀ : x₀ ∈ Ω) (hmin : IsLocalMin (fun y => lbar u y - φ y) x₀)
    (hg : gradient φ x₀ ≠ 0) :
    0 ≤ viscF p (gradient φ x₀) (hess φ x₀) := by
  obtain ⟨R, hR, hcb⟩ := exists_closedBall_subset hΩ hx₀
  obtain ⟨ψ, r, hr, hrR, hψ, hψb, ⟨B, hB⟩, hstrict, hgrad, hhess⟩ :=
    regularize (V := ubar (fun ε y => -u ε y)) (contDiff_neg' hφ)
      (localMax_neg_of_localMin hmin) hR
  have hΩr : closedBall x₀ r ⊆ Ω :=
    (closedBall_subset_closedBall hrR).trans hcb
  have hgψ : gradient ψ x₀ ≠ 0 := by
    rw [hgrad]; exact gradient_neg_ne_zero hg
  have hCn : ∀ ε y, |(fun ε y => -u ε y) ε y| ≤ C := by
    intro ε y; simp only; rw [abs_neg]; exact hC ε y
  have hun : ∀ ε > 0, IsPHarmonious p ε Ω (fun y => -F y)
      ((fun ε y => -u ε y) ε) :=
    fun ε hε => isPHarmonious_neg (hu ε hε)
  have h := regular_subsol hd hp hpd hCn hun hψ hψb hB hr hΩr hstrict hgψ
  rw [hgrad, hhess, normPLapOf_neg] at h
  rw [viscF_eq_neg, hess_eq_fderiv]
  linarith

/-- **The singular supersolution field**, through the negated family. -/
theorem visc_sing_super [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} (hΩ : IsOpen Ω) {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε))
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ) {x₀ : EuclSpace d}
    (hx₀ : x₀ ∈ Ω) (hmin : IsLocalMin (fun y => lbar u y - φ y) x₀) :
    0 ≤ viscFUpper p (hess φ x₀) := by
  obtain ⟨R, hR, hcb⟩ := exists_closedBall_subset hΩ hx₀
  obtain ⟨ψ, r, hr, hrR, hψ, hψb, ⟨B, hB⟩, hstrict, _hgrad, hhess⟩ :=
    regularize (V := ubar (fun ε y => -u ε y)) (contDiff_neg' hφ)
      (localMax_neg_of_localMin hmin) hR
  have hΩr : closedBall x₀ r ⊆ Ω :=
    (closedBall_subset_closedBall hrR).trans hcb
  have hCn : ∀ ε y, |(fun ε y => -u ε y) ε y| ≤ C := by
    intro ε y; simp only; rw [abs_neg]; exact hC ε y
  have hun : ∀ ε > 0, IsPHarmonious p ε Ω (fun y => -F y)
      ((fun ε y => -u ε y) ε) :=
    fun ε hε => isPHarmonious_neg (hu ε hε)
  have h := singular_subsol hd hp hpd hCn hun hψ hψb hB hr hΩr hstrict
  unfold viscFLower at h
  unfold viscFUpper
  rw [hess_eq_fderiv, hhess, hess_neg, laplacianOf_neg, lamMax_neg] at h
  rw [hess_eq_fderiv]
  linarith

/-- **The upper relaxed limit is a viscosity subsolution**, for `C³` test
functions. -/
theorem ubar_isViscositySubsolution3 [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} (hΩ : IsOpen Ω) {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε)) :
    IsViscositySubsolution3 p Ω (fun _ => 0) (ubar u) :=
  ⟨(upperSemicontinuous_ubar u hC).upperSemicontinuousOn _,
   fun _φ hφ _x₀ hx₀ hmax hg =>
     visc_reg_sub hd hp hpd hΩ hC hu hφ hx₀ hmax hg,
   fun _φ hφ _x₀ hx₀ hmax _ =>
     visc_sing_sub hd hp hpd hΩ hC hu hφ hx₀ hmax⟩

/-- **The lower relaxed limit is a viscosity supersolution**, for `C³` test
functions. -/
theorem lbar_isViscositySupersolution3 [Nontrivial (EuclSpace d)]
    (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} (hΩ : IsOpen Ω) {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε)) :
    IsViscositySupersolution3 p Ω (fun _ => 0) (lbar u) :=
  ⟨(lowerSemicontinuous_lbar u hC).lowerSemicontinuousOn _,
   fun _φ hφ _x₀ hx₀ hmin hg =>
     visc_reg_super hd hp hpd hΩ hC hu hφ hx₀ hmin hg,
   fun _φ hφ _x₀ hx₀ hmin _ =>
     visc_sing_super hd hp hpd hΩ hC hu hφ hx₀ hmin⟩

end

end PLaplacian
