/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.TaylorTest

/-!
# The viscosity property

The upper relaxed limit of a uniformly bounded family of p-harmonious
functions is a viscosity subsolution, and the lower relaxed limit a viscosity
supersolution, of the homogeneous normalized p-Laplace equation, in the sense
of the layer-two predicates with C two test functions.

Every operator in the predicates sees the Hessian only through its quadratic
form, so a shift of that form by a multiple of the squared norm shifts each
generator by an explicit amount. A C two test function is replaced by its
Taylor polynomial plus a small multiple of the squared distance, which is
smooth and still touches; the C three theorems apply to it, and letting the
multiple tend to zero gives the inequality for the original. No symmetry of
the Hessian is needed.

## Main results

- laplacianOf_shift, infLaplacianOf_shift, lamMax_shift, lamMin_shift
- viscF_shift, viscFLower_shift, viscFUpper_shift
- visc2_reg_sub, visc2_sing_sub, visc2_reg_super, visc2_sing_super
- ubar_isViscositySubsolution
- lbar_isViscositySupersolution
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The viscosity property, for `C²` test functions

The upper relaxed limit is a viscosity subsolution and the lower relaxed limit
a viscosity supersolution, in the sense of the layer-two predicates
themselves, with `C²` test functions.

## The shift

Every operator in the predicates sees the Hessian only through its quadratic
form `v ↦ X(v,v)`: the trace sums it over a basis, the infinity Laplacian
evaluates it at the unit gradient, the extreme eigenvalues take its supremum
and infimum over the unit sphere. So if `Y(v,v) = X(v,v) + 2κ ‖v‖²`, each
shifts by an explicit amount, and every generator drops by `2κ(d + p - 2)`.

## The reduction

For a `C²` test function, the Taylor test function with `κ = η` touches from
above, and its Hessian quadratic form is the original plus `2η ‖v‖²`. The
`C³` theorems give `viscF(X) - 2η(d+p-2) ≤ 0` for every `η > 0`, hence
`viscF(X) ≤ 0`. Touching from below uses `κ = -η`.

No symmetry of the Hessian is needed, because no operator depends on more than
its quadratic form.
-/

/-- The quadratic form on the unit sphere is bounded below. -/
theorem bddBelow_quad_sphere (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) :
    BddBelow ((fun v => (X v) v) '' {v : EuclSpace d | ‖v‖ = 1}) := by
  refine ⟨-‖X‖, ?_⟩
  rintro a ⟨w, hw, rfl⟩
  have hw' : ‖w‖ = 1 := hw
  have h1 := X.le_opNorm w
  have h2 := (X w).le_opNorm w
  have h3 : |(X w) w| ≤ ‖X‖ := by
    calc |(X w) w| = ‖(X w) w‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖X w‖ * ‖w‖ := h2
      _ ≤ (‖X‖ * ‖w‖) * ‖w‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖X‖ := by rw [hw']; ring
  exact (abs_le.1 h3).1

/-- The unit sphere is nonempty in positive dimension. -/
theorem sphere_nonempty (hd : 0 < d) :
    {v : EuclSpace d | ‖v‖ = 1}.Nonempty :=
  ⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) 1, by simp⟩

section shift

variable {X Y : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ} {κ : ℝ}

theorem laplacianOf_shift (hYX : ∀ v, (Y v) v = (X v) v + 2 * κ * ‖v‖ ^ 2) :
    laplacianOf Y = laplacianOf X + 2 * κ * d := by
  unfold laplacianOf
  have h : ∀ i : Fin d,
      (Y (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1)
        = (X (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1)
          + 2 * κ := by
    intro i; rw [hYX]; simp
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib]
  simp [Finset.sum_const]
  ring

theorem infLaplacianOf_shift (hYX : ∀ v, (Y v) v = (X v) v + 2 * κ * ‖v‖ ^ 2)
    {q : EuclSpace d} (hq : q ≠ 0) :
    infLaplacianOf q Y = infLaplacianOf q X + 2 * κ := by
  unfold infLaplacianOf
  rw [hYX]
  have hn : ‖‖q‖⁻¹ • q‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hq)]
  rw [hn]; ring

theorem lamMax_shift (hd : 0 < d)
    (hYX : ∀ v, (Y v) v = (X v) v + 2 * κ * ‖v‖ ^ 2) :
    lamMax Y = lamMax X + 2 * κ := by
  unfold lamMax
  have hS := sphere_nonempty hd
  have hbX := bddAbove_quad_sphere X
  have hbY := bddAbove_quad_sphere Y
  have hv : ∀ v ∈ {v : EuclSpace d | ‖v‖ = 1}, (Y v) v = (X v) v + 2 * κ := by
    intro v hvS
    have : ‖v‖ = 1 := hvS
    rw [hYX, this]; ring
  apply le_antisymm
  · apply csSup_le (hS.image _)
    rintro _ ⟨v, hvS, rfl⟩
    show (Y v) v ≤ _
    rw [hv v hvS]
    have := le_csSup hbX ⟨v, hvS, rfl⟩
    linarith
  · have hle : sSup ((fun v => (X v) v) '' {v : EuclSpace d | ‖v‖ = 1})
        ≤ sSup ((fun v => (Y v) v) '' {v : EuclSpace d | ‖v‖ = 1}) - 2 * κ := by
      apply csSup_le (hS.image _)
      rintro _ ⟨v, hvS, rfl⟩
      show (X v) v ≤ _
      have h1 : (Y v) v ≤ sSup ((fun v => (Y v) v) '' {v : EuclSpace d | ‖v‖ = 1}) :=
        le_csSup hbY ⟨v, hvS, rfl⟩
      rw [hv v hvS] at h1
      linarith
    linarith

theorem lamMin_shift (hd : 0 < d)
    (hYX : ∀ v, (Y v) v = (X v) v + 2 * κ * ‖v‖ ^ 2) :
    lamMin Y = lamMin X + 2 * κ := by
  unfold lamMin
  have hS := sphere_nonempty hd
  have hbX := bddBelow_quad_sphere X
  have hbY := bddBelow_quad_sphere Y
  have hv : ∀ v ∈ {v : EuclSpace d | ‖v‖ = 1}, (Y v) v = (X v) v + 2 * κ := by
    intro v hvS
    have : ‖v‖ = 1 := hvS
    rw [hYX, this]; ring
  apply le_antisymm
  · have hle : sInf ((fun v => (Y v) v) '' {v : EuclSpace d | ‖v‖ = 1}) - 2 * κ
        ≤ sInf ((fun v => (X v) v) '' {v : EuclSpace d | ‖v‖ = 1}) := by
      apply le_csInf (hS.image _)
      rintro _ ⟨v, hvS, rfl⟩
      show _ ≤ (X v) v
      have h1 : sInf ((fun v => (Y v) v) '' {v : EuclSpace d | ‖v‖ = 1}) ≤ (Y v) v :=
        csInf_le hbY ⟨v, hvS, rfl⟩
      rw [hv v hvS] at h1
      linarith
    linarith
  · apply le_csInf (hS.image _)
    rintro _ ⟨v, hvS, rfl⟩
    show _ ≤ (Y v) v
    rw [hv v hvS]
    have := csInf_le hbX ⟨v, hvS, rfl⟩
    linarith

theorem viscF_shift (hYX : ∀ v, (Y v) v = (X v) v + 2 * κ * ‖v‖ ^ 2)
    {p : ℝ} {q : EuclSpace d} (hq : q ≠ 0) :
    viscF p q Y = viscF p q X - 2 * κ * ((d : ℝ) + p - 2) := by
  rw [viscF_eq_neg, viscF_eq_neg]
  unfold normPLapOf
  rw [laplacianOf_shift hYX, infLaplacianOf_shift hYX hq]
  ring

theorem viscFLower_shift (hd : 0 < d)
    (hYX : ∀ v, (Y v) v = (X v) v + 2 * κ * ‖v‖ ^ 2) {p : ℝ} :
    viscFLower p Y = viscFLower p X - 2 * κ * ((d : ℝ) + p - 2) := by
  unfold viscFLower
  rw [laplacianOf_shift hYX, lamMax_shift hd hYX]
  ring

theorem viscFUpper_shift (hd : 0 < d)
    (hYX : ∀ v, (Y v) v = (X v) v + 2 * κ * ‖v‖ ^ 2) {p : ℝ} :
    viscFUpper p Y = viscFUpper p X - 2 * κ * ((d : ℝ) + p - 2) := by
  unfold viscFUpper
  rw [laplacianOf_shift hYX, lamMin_shift hd hYX]
  ring

end shift

/-- A quantity bounded by every positive multiple of a positive constant is
nonpositive. -/
theorem nonpos_of_forall_le_mul {a D : ℝ} (hD : 0 < D)
    (h : ∀ η > 0, a ≤ 2 * η * D) : a ≤ 0 := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  have h1 := h (ε / (2 * D)) (by positivity)
  have h2 : 2 * (ε / (2 * D)) * D = ε := by field_simp
  linarith

theorem dim_pos {p : ℝ} (hd : 0 < d) (hp : 2 ≤ p) : 0 < (d : ℝ) + p - 2 := by
  have : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

/-- **The regular subsolution field, for `C²` test functions.** -/
theorem visc2_reg_sub [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} (hΩ : IsOpen Ω) {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε))
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ) {x₀ : EuclSpace d}
    (hx₀ : x₀ ∈ Ω) (hmax : IsLocalMax (fun y => ubar u y - φ y) x₀)
    (hg : gradient φ x₀ ≠ 0) :
    viscF p (gradient φ x₀) (hess φ x₀) ≤ 0 := by
  have key : ∀ η > 0, viscF p (gradient φ x₀) (hess φ x₀)
      ≤ 2 * η * ((d : ℝ) + p - 2) := by
    intro η hη
    have hgP : gradient (tPoly φ x₀ η) x₀ ≠ 0 := by
      rw [gradient_tPoly_self]; exact hg
    have h := visc_reg_sub hd hp hpd hΩ hC hu (contDiff_tPoly φ x₀ η) hx₀
      (localMax_tPoly hφ hmax hη) hgP
    rw [gradient_tPoly_self] at h
    rw [viscF_shift (X := hess φ x₀) (fun v => hess_tPoly_quad φ x₀ v η) hg] at h
    linarith
  exact nonpos_of_forall_le_mul (dim_pos hd hp) key

/-- **The singular subsolution field, for `C²` test functions.** -/
theorem visc2_sing_sub [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} (hΩ : IsOpen Ω) {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε))
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ) {x₀ : EuclSpace d}
    (hx₀ : x₀ ∈ Ω) (hmax : IsLocalMax (fun y => ubar u y - φ y) x₀) :
    viscFLower p (hess φ x₀) ≤ 0 := by
  have key : ∀ η > 0, viscFLower p (hess φ x₀)
      ≤ 2 * η * ((d : ℝ) + p - 2) := by
    intro η hη
    have h := visc_sing_sub hd hp hpd hΩ hC hu (contDiff_tPoly φ x₀ η) hx₀
      (localMax_tPoly hφ hmax hη)
    rw [viscFLower_shift (X := hess φ x₀) hd
      (fun v => hess_tPoly_quad φ x₀ v η)] at h
    linarith
  exact nonpos_of_forall_le_mul (dim_pos hd hp) key

/-- **The regular supersolution field, for `C²` test functions.** -/
theorem visc2_reg_super [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} (hΩ : IsOpen Ω) {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε))
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ) {x₀ : EuclSpace d}
    (hx₀ : x₀ ∈ Ω) (hmin : IsLocalMin (fun y => lbar u y - φ y) x₀)
    (hg : gradient φ x₀ ≠ 0) :
    0 ≤ viscF p (gradient φ x₀) (hess φ x₀) := by
  have key : ∀ η > 0, -viscF p (gradient φ x₀) (hess φ x₀)
      ≤ 2 * η * ((d : ℝ) + p - 2) := by
    intro η hη
    have hgP : gradient (tPoly φ x₀ (-η)) x₀ ≠ 0 := by
      rw [gradient_tPoly_self]; exact hg
    have h := visc_reg_super hd hp hpd hΩ hC hu (contDiff_tPoly φ x₀ (-η))
      hx₀ (localMin_tPoly hφ hmin hη) hgP
    rw [gradient_tPoly_self] at h
    rw [viscF_shift (X := hess φ x₀) (fun v => hess_tPoly_quad φ x₀ v (-η))
      hg] at h
    linarith
  linarith [nonpos_of_forall_le_mul (dim_pos hd hp) key]

/-- **The singular supersolution field, for `C²` test functions.** -/
theorem visc2_sing_super [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} (hΩ : IsOpen Ω) {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε))
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ) {x₀ : EuclSpace d}
    (hx₀ : x₀ ∈ Ω) (hmin : IsLocalMin (fun y => lbar u y - φ y) x₀) :
    0 ≤ viscFUpper p (hess φ x₀) := by
  have key : ∀ η > 0, -viscFUpper p (hess φ x₀)
      ≤ 2 * η * ((d : ℝ) + p - 2) := by
    intro η hη
    have h := visc_sing_super hd hp hpd hΩ hC hu (contDiff_tPoly φ x₀ (-η))
      hx₀ (localMin_tPoly hφ hmin hη)
    rw [viscFUpper_shift (X := hess φ x₀) hd
      (fun v => hess_tPoly_quad φ x₀ v (-η))] at h
    linarith
  linarith [nonpos_of_forall_le_mul (dim_pos hd hp) key]

/-- **The upper relaxed limit is a viscosity subsolution** of the homogeneous
normalized `p`-Laplace equation, in the sense of the layer-two predicate. -/
theorem ubar_isViscositySubsolution [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} (hΩ : IsOpen Ω) {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε)) :
    IsViscositySubsolution p Ω (fun _ => 0) (ubar u) :=
  ⟨(upperSemicontinuous_ubar u hC).upperSemicontinuousOn _,
   fun _φ hφ _x₀ hx₀ hmax hg =>
     visc2_reg_sub hd hp hpd hΩ hC hu hφ hx₀ hmax hg,
   fun _φ hφ _x₀ hx₀ hmax _ =>
     visc2_sing_sub hd hp hpd hΩ hC hu hφ hx₀ hmax⟩

/-- **The lower relaxed limit is a viscosity supersolution** of the homogeneous
normalized `p`-Laplace equation, in the sense of the layer-two predicate. -/
theorem lbar_isViscositySupersolution [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} (hΩ : IsOpen Ω) {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε)) :
    IsViscositySupersolution p Ω (fun _ => 0) (lbar u) :=
  ⟨(lowerSemicontinuous_lbar u hC).lowerSemicontinuousOn _,
   fun _φ hφ _x₀ hx₀ hmin hg =>
     visc2_reg_super hd hp hpd hΩ hC hu hφ hx₀ hmin hg,
   fun _φ hφ _x₀ hx₀ hmin _ =>
     visc2_sing_super hd hp hpd hΩ hC hu hφ hx₀ hmin⟩

end

end PLaplacian
