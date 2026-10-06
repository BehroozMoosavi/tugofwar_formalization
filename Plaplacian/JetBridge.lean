/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Jets

/-! # From the viscosity predicates to jets

The predicates are stated with test functions; the theorem of sums produces
jets. The bridge is the jet polynomial

  `J w = c + ⟪q, w - x⟫ + ½ X(w - x, w - x) + κ ‖w - x‖²`,

smooth, with gradient `q` at `x` and quadratic form `X(v,v) + 2κ ‖v‖²`. A
superjet condition says exactly that `u ≤ J` near `x` for `κ = η > 0`, so `J`
is a valid test function, and the predicate gives
`F(q, X) - 2η(d + p - 2) ≤ f x` for every `η`, hence `F(q, X) ≤ f x`.

This replaces the usual construction of a `C²` test function from a modulus of
continuity, which is the one fiddly step in the standard equivalence of the two
definitions. The quadratic-form shift, proved for the reduction from `C²` to
`C³`, does the work again.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}




/-- **The jet polynomial.** -/
def jPoly (c : ℝ) (x q : EuclSpace d) (X : Bilin d) (κ : ℝ) :
    EuclSpace d → ℝ := fun w =>
  c + inner ℝ q (w - x) + (1 / 2) * (X (w - x)) (w - x) + κ * ‖w - x‖ ^ 2

theorem contDiff_jPoly (c : ℝ) (x q : EuclSpace d) (X : Bilin d) (κ : ℝ)
    {n : WithTop ℕ∞} : ContDiff ℝ n (jPoly c x q X κ) := by
  unfold jPoly
  have h1 : ContDiff ℝ n (fun w : EuclSpace d => w - x) :=
    contDiff_id.sub contDiff_const
  have hI : ContDiff ℝ n (fun w : EuclSpace d => inner ℝ q (w - x)) :=
    ContDiff.inner ℝ contDiff_const h1
  have hX : ContDiff ℝ n (fun w => (X (w - x)) (w - x)) :=
    (X.contDiff.comp h1).clm_apply h1
  have hN : ContDiff ℝ n (fun w => ‖w - x‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp h1
  exact ((contDiff_const.add hI).add (contDiff_const.mul hX)).add
    (contDiff_const.mul hN)

theorem jPoly_self (c : ℝ) (x q : EuclSpace d) (X : Bilin d) (κ : ℝ) :
    jPoly c x q X κ x = c := by
  simp [jPoly]

/-- Along a line through the base point, the jet polynomial is a quadratic in
the parameter. -/
theorem jPoly_line (c : ℝ) (x q z : EuclSpace d) (X : Bilin d) (κ s : ℝ) :
    jPoly c x q X κ (x + s • z)
      = c + s * inner ℝ q z + s ^ 2 * ((1 / 2) * (X z) z + κ * ‖z‖ ^ 2) := by
  unfold jPoly
  have hsub : x + s • z - x = s • z := by abel
  rw [hsub]
  simp only [inner_smul_right, map_smul, smul_eq_mul, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs, smul_apply]
  ring

theorem jPoly_line_fun (c : ℝ) (x q z : EuclSpace d) (X : Bilin d) (κ : ℝ) :
    (fun s : ℝ => jPoly c x q X κ (x + s • z))
      = fun s => c + s * inner ℝ q z
          + s ^ 2 * ((1 / 2) * (X z) z + κ * ‖z‖ ^ 2) := by
  funext s; exact jPoly_line c x q z X κ s

/-- **Its derivative at the base point is the functional of `q`.** -/
theorem fderiv_jPoly_self (c : ℝ) (x q : EuclSpace d) (X : Bilin d) (κ : ℝ) :
    fderiv ℝ (jPoly c x q X κ) x = InnerProductSpace.toDual ℝ (EuclSpace d) q := by
  ext z
  rw [← line_deriv_one (contDiff_jPoly c x q X κ) x z,
    jPoly_line_fun, deriv_quad_poly]
  simp

/-- **Its gradient at the base point is `q`.** -/
theorem gradient_jPoly_self (c : ℝ) (x q : EuclSpace d) (X : Bilin d)
    (κ : ℝ) : gradient (jPoly c x q X κ) x = q := by
  unfold gradient
  rw [fderiv_jPoly_self]
  exact LinearIsometryEquiv.symm_apply_apply _ _

/-- **Its Hessian quadratic form is `X` plus `2κ ‖z‖²`.** -/
theorem hess_jPoly_quad (c : ℝ) (x q z : EuclSpace d) (X : Bilin d) (κ : ℝ) :
    fderiv ℝ (fderiv ℝ (jPoly c x q X κ)) x z z = (X z) z + 2 * κ * ‖z‖ ^ 2 := by
  rw [← line_deriv_two (contDiff_jPoly c x q X κ) x z,
    jPoly_line_fun, deriv_deriv_quad_poly]
  ring

/-- **A superjet gives a jet polynomial touching from above.** -/
theorem localMax_jPoly {u : EuclSpace d → ℝ} {x q : EuclSpace d} {X : Bilin d}
    (hj : (q, X) ∈ SuperJet u x) {η : ℝ} (hη : 0 < η) :
    IsLocalMax (fun y => u y - jPoly (u x) x q X η y) x := by
  have h := hj η hη
  unfold IsLocalMax IsMaxFilter
  filter_upwards [h] with y hy
  change u y - jPoly (u x) x q X η y ≤ u x - jPoly (u x) x q X η x
  rw [jPoly_self]
  simp only [jPoly]
  linarith

/-- **A subjet gives a jet polynomial touching from below.** -/
theorem localMin_jPoly {u : EuclSpace d → ℝ} {x q : EuclSpace d} {X : Bilin d}
    (hj : (q, X) ∈ SubJet u x) {η : ℝ} (hη : 0 < η) :
    IsLocalMin (fun y => u y - jPoly (u x) x q X (-η) y) x := by
  have h := hj η hη
  unfold IsLocalMin IsMinFilter
  filter_upwards [h] with y hy
  change u x - jPoly (u x) x q X (-η) x ≤ u y - jPoly (u x) x q X (-η) y
  rw [jPoly_self]
  simp only [jPoly]
  linarith

section bridge

variable {p : ℝ} {Ω : Set (EuclSpace d)} {f u : EuclSpace d → ℝ}
  {x q : EuclSpace d} {X : Bilin d}

/-- **The regular subsolution inequality at a superjet.** -/
theorem superJet_regular (hd : 0 < d) (hp : 2 ≤ p)
    (hsub : IsViscositySubsolution p Ω f u) (hx : x ∈ Ω)
    (hj : (q, X) ∈ SuperJet u x) (hq : q ≠ 0) :
    viscF p q X ≤ f x := by
  have key : ∀ η > 0, viscF p q X - f x ≤ 2 * η * ((d : ℝ) + p - 2) := by
    intro η hη
    have hg : gradient (jPoly (u x) x q X η) x ≠ 0 := by
      rw [gradient_jPoly_self]; exact hq
    have h := hsub.regular _ (contDiff_jPoly (u x) x q X η) x hx
      (localMax_jPoly hj hη) hg
    rw [gradient_jPoly_self] at h
    rw [viscF_shift (X := X) (fun v => hess_jPoly_quad (u x) x q v X η) hq] at h
    linarith
  linarith [nonpos_of_forall_le_mul (dim_pos hd hp) key]

/-- **The singular subsolution inequality at a superjet.** -/
theorem superJet_singular (hd : 0 < d) (hp : 2 ≤ p)
    (hsub : IsViscositySubsolution p Ω f u) (hx : x ∈ Ω)
    (hj : (0, X) ∈ SuperJet u x) :
    viscFLower p X ≤ f x := by
  have key : ∀ η > 0, viscFLower p X - f x ≤ 2 * η * ((d : ℝ) + p - 2) := by
    intro η hη
    have hg : gradient (jPoly (u x) x 0 X η) x = 0 := gradient_jPoly_self _ _ _ _ _
    have h := hsub.singular _ (contDiff_jPoly (u x) x 0 X η) x hx
      (localMax_jPoly hj hη) hg
    rw [viscFLower_shift (X := X) hd
      (fun v => hess_jPoly_quad (u x) x 0 v X η)] at h
    linarith
  linarith [nonpos_of_forall_le_mul (dim_pos hd hp) key]

/-- **The regular supersolution inequality at a subjet.** -/
theorem subJet_regular (hd : 0 < d) (hp : 2 ≤ p)
    (hsup : IsViscositySupersolution p Ω f u) (hx : x ∈ Ω)
    (hj : (q, X) ∈ SubJet u x) (hq : q ≠ 0) :
    f x ≤ viscF p q X := by
  have key : ∀ η > 0, f x - viscF p q X ≤ 2 * η * ((d : ℝ) + p - 2) := by
    intro η hη
    have hg : gradient (jPoly (u x) x q X (-η)) x ≠ 0 := by
      rw [gradient_jPoly_self]; exact hq
    have h := hsup.regular _ (contDiff_jPoly (u x) x q X (-η)) x hx
      (localMin_jPoly hj hη) hg
    rw [gradient_jPoly_self] at h
    rw [viscF_shift (X := X) (fun v => hess_jPoly_quad (u x) x q v X (-η)) hq]
      at h
    linarith
  linarith [nonpos_of_forall_le_mul (dim_pos hd hp) key]

/-- **The singular supersolution inequality at a subjet.** -/
theorem subJet_singular (hd : 0 < d) (hp : 2 ≤ p)
    (hsup : IsViscositySupersolution p Ω f u) (hx : x ∈ Ω)
    (hj : (0, X) ∈ SubJet u x) :
    f x ≤ viscFUpper p X := by
  have key : ∀ η > 0, f x - viscFUpper p X ≤ 2 * η * ((d : ℝ) + p - 2) := by
    intro η hη
    have hg : gradient (jPoly (u x) x 0 X (-η)) x = 0 :=
      gradient_jPoly_self _ _ _ _ _
    have h := hsup.singular _ (contDiff_jPoly (u x) x 0 X (-η)) x hx
      (localMin_jPoly hj hη) hg
    rw [viscFUpper_shift (X := X) hd
      (fun v => hess_jPoly_quad (u x) x 0 v X (-η))] at h
    linarith
  linarith [nonpos_of_forall_le_mul (dim_pos hd hp) key]

end bridge

end

end PLaplacian
