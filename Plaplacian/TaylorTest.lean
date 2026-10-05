/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.ViscC3

/-!
# The Taylor polynomial as a test function

A C two test function touching at the base point is replaced by its
second-order Taylor polynomial plus a multiple of the squared distance. The
result is a polynomial, so smooth; with a positive multiple the C two Taylor
estimate at the fixed base point keeps it touching from above, and with a
negative one from below. Its derivatives are computed along lines, where it is
an explicit quadratic in the parameter: its gradient at the base point is the
original, and its Hessian quadratic form is the original plus twice the
multiple times the squared norm.

## Main results

- line_deriv_one, line_deriv_two
- tPoly, contDiff_tPoly, tPoly_self, tPoly_line
- fderiv_tPoly_self, gradient_tPoly_self, hess_tPoly_quad
- localMax_tPoly, localMin_tPoly
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The Taylor polynomial as a test function

The reduction from `C²` to `C³` test functions. A `C²` test function touching
at `x₀` is replaced by its second-order Taylor polynomial plus `κ ‖w - x₀‖²`:

  `P w = φ x₀ + Dφ(x₀)(w - x₀) + ½ D²φ(x₀)(w - x₀, w - x₀) + κ ‖w - x₀‖²`.

This is a polynomial, so smooth. With `κ = η > 0`, the `C²` Taylor estimate at
the fixed point `x₀` gives `φ ≤ P` near `x₀`, so `P` still touches from above;
with `κ = -η`, it touches from below.

Its derivatives are computed along lines: `s ↦ P (x₀ + s z)` is an explicit
quadratic in `s`, whose first derivative at zero gives the gradient and whose
second gives the quadratic form `X(z,z) + 2κ ‖z‖²`.
-/


/-- The first derivative along a line, for a `C²` function. -/
theorem line_deriv_one {ψ : EuclSpace d → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (x z : EuclSpace d) :
    deriv (fun s : ℝ => ψ (x + s • z)) 0 = fderiv ℝ ψ x z := by
  have h := hasDerivAt_first hψ x z 0
  simp only [lineMap, zero_smul, add_zero] at h
  exact h.deriv

/-- The second derivative along a line, for a `C²` function. -/
theorem line_deriv_two {ψ : EuclSpace d → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (x z : EuclSpace d) :
    deriv (deriv (fun s : ℝ => ψ (x + s • z))) 0
      = fderiv ℝ (fderiv ℝ ψ) x z z := by
  have h := hasDerivAt_second_at hψ x z 0
  simp only [lineMap, zero_smul, add_zero] at h
  have hfun : deriv (fun s : ℝ => ψ (x + s • z))
      = fun t => fderiv ℝ ψ (x + t • z) z := by
    funext t
    have ht := hasDerivAt_first hψ x z t
    simp only [lineMap] at ht
    exact ht.deriv
  rw [hfun]
  exact h.deriv

/-- The first derivative of a quadratic polynomial at zero. -/
theorem hasDerivAt_quad_poly (a b c t : ℝ) :
    HasDerivAt (fun s : ℝ => a + s * b + s ^ 2 * c) (b + 2 * t * c) t := by
  have h := ((hasDerivAt_const t a).add ((hasDerivAt_id' t).mul_const b)).add
    ((hasDerivAt_pow 2 t).mul_const c)
  have hfun : (fun s : ℝ => a + s * b + s ^ 2 * c)
      = ((fun _ : ℝ => a) + fun y : ℝ => y * b) + fun y : ℝ => y ^ 2 * c := by
    funext s; simp
  rw [hfun]
  exact h.congr_deriv (by norm_num)

theorem deriv_quad_poly (a b c : ℝ) :
    deriv (fun s : ℝ => a + s * b + s ^ 2 * c) 0 = b := by
  rw [(hasDerivAt_quad_poly a b c 0).deriv]; ring

theorem deriv_deriv_quad_poly (a b c : ℝ) :
    deriv (deriv (fun s : ℝ => a + s * b + s ^ 2 * c)) 0 = 2 * c := by
  have hfun : deriv (fun s : ℝ => a + s * b + s ^ 2 * c)
      = fun t => b + 2 * t * c := by
    funext t; exact (hasDerivAt_quad_poly a b c t).deriv
  rw [hfun]
  have h0 := (hasDerivAt_const (0:ℝ) b).add
    (((hasDerivAt_id' (0:ℝ)).const_mul 2).mul_const c)
  have hfun2 : (fun t : ℝ => b + 2 * t * c)
      = (fun _ : ℝ => b) + fun y : ℝ => 2 * y * c := by
    funext t; simp
  rw [hfun2]
  exact (h0.congr_deriv (by norm_num)).deriv

/-- **The Taylor test function.** -/
def tPoly (φ : EuclSpace d → ℝ) (x₀ : EuclSpace d) (κ : ℝ) :
    EuclSpace d → ℝ := fun w =>
  φ x₀ + fderiv ℝ φ x₀ (w - x₀)
    + (1 / 2) * fderiv ℝ (fderiv ℝ φ) x₀ (w - x₀) (w - x₀)
    + κ * ‖w - x₀‖ ^ 2

theorem contDiff_tPoly (φ : EuclSpace d → ℝ) (x₀ : EuclSpace d) (κ : ℝ)
    {n : WithTop ℕ∞} : ContDiff ℝ n (tPoly φ x₀ κ) := by
  unfold tPoly
  have h1 : ContDiff ℝ n (fun w : EuclSpace d => w - x₀) :=
    contDiff_id.sub contDiff_const
  have hL : ContDiff ℝ n (fun w => fderiv ℝ φ x₀ (w - x₀)) :=
    (fderiv ℝ φ x₀).contDiff.comp h1
  have hX : ContDiff ℝ n
      (fun w => fderiv ℝ (fderiv ℝ φ) x₀ (w - x₀) (w - x₀)) :=
    ((fderiv ℝ (fderiv ℝ φ) x₀).contDiff.comp h1).clm_apply h1
  have hN : ContDiff ℝ n (fun w => ‖w - x₀‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp h1
  exact ((contDiff_const.add hL).add (contDiff_const.mul hX)).add
    (contDiff_const.mul hN)

theorem tPoly_self (φ : EuclSpace d → ℝ) (x₀ : EuclSpace d) (κ : ℝ) :
    tPoly φ x₀ κ x₀ = φ x₀ := by
  simp [tPoly]

/-- Along a line through the base point, the Taylor test function is a
quadratic in the parameter. -/
theorem tPoly_line (φ : EuclSpace d → ℝ) (x₀ z : EuclSpace d) (κ s : ℝ) :
    tPoly φ x₀ κ (x₀ + s • z)
      = φ x₀ + s * fderiv ℝ φ x₀ z
        + s ^ 2 * ((1 / 2) * fderiv ℝ (fderiv ℝ φ) x₀ z z + κ * ‖z‖ ^ 2) := by
  unfold tPoly
  have hsub : x₀ + s • z - x₀ = s • z := by abel
  rw [hsub]
  simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, ContinuousLinearMap.smul_apply]
  ring

/-- **Its gradient at the base point is that of the original.** -/
theorem fderiv_tPoly_self (φ : EuclSpace d → ℝ) (x₀ : EuclSpace d) (κ : ℝ) :
    fderiv ℝ (tPoly φ x₀ κ) x₀ = fderiv ℝ φ x₀ := by
  ext z
  rw [← line_deriv_one (contDiff_tPoly φ x₀ κ) x₀ z]
  have hline : (fun s : ℝ => tPoly φ x₀ κ (x₀ + s • z))
      = fun s => φ x₀ + s * fderiv ℝ φ x₀ z
        + s ^ 2 * ((1 / 2) * fderiv ℝ (fderiv ℝ φ) x₀ z z + κ * ‖z‖ ^ 2) := by
    funext s; exact tPoly_line φ x₀ z κ s
  rw [hline, deriv_quad_poly]

theorem gradient_tPoly_self (φ : EuclSpace d → ℝ) (x₀ : EuclSpace d)
    (κ : ℝ) : gradient (tPoly φ x₀ κ) x₀ = gradient φ x₀ := by
  unfold gradient; rw [fderiv_tPoly_self]

/-- **Its Hessian quadratic form is the original's plus `2κ‖z‖²`.** -/
theorem hess_tPoly_quad (φ : EuclSpace d → ℝ) (x₀ z : EuclSpace d) (κ : ℝ) :
    fderiv ℝ (fderiv ℝ (tPoly φ x₀ κ)) x₀ z z
      = fderiv ℝ (fderiv ℝ φ) x₀ z z + 2 * κ * ‖z‖ ^ 2 := by
  rw [← line_deriv_two (contDiff_tPoly φ x₀ κ) x₀ z]
  have hline : (fun s : ℝ => tPoly φ x₀ κ (x₀ + s • z))
      = fun s => φ x₀ + s * fderiv ℝ φ x₀ z
        + s ^ 2 * ((1 / 2) * fderiv ℝ (fderiv ℝ φ) x₀ z z + κ * ‖z‖ ^ 2) := by
    funext s; exact tPoly_line φ x₀ z κ s
  rw [hline, deriv_deriv_quad_poly]
  ring

/-- **Touching from above.** If `U - φ` has a local maximum at `x₀`, so does
`U` minus the Taylor test function with positive `κ`. -/
theorem localMax_tPoly {U φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    {x₀ : EuclSpace d} (hmax : IsLocalMax (fun y => U y - φ y) x₀)
    {η : ℝ} (hη : 0 < η) :
    IsLocalMax (fun y => U y - tPoly φ x₀ η y) x₀ := by
  obtain ⟨δ, hδ, hT⟩ := exists_taylorErr_le hφ x₀ hη
  unfold IsLocalMax IsMaxFilter at hmax ⊢
  filter_upwards [hmax, Metric.ball_mem_nhds x₀ hδ] with y hy hyb
  change U y - φ y ≤ U x₀ - φ x₀ at hy
  change U y - tPoly φ x₀ η y ≤ U x₀ - tPoly φ x₀ η x₀
  have hz : ‖y - x₀‖ < δ := by rw [mem_ball, dist_eq_norm] at hyb; exact hyb
  have herr := (abs_le.1 (hT (y - x₀) hz)).2
  have hdec := decomp_at φ x₀ (y - x₀)
  have hxy : x₀ + (y - x₀) = y := by abel
  rw [hxy] at hdec
  rw [tPoly_self]
  simp only [tPoly]
  linarith

/-- **Touching from below.** If `U - φ` has a local minimum at `x₀`, so does
`U` minus the Taylor test function with negative `κ`. -/
theorem localMin_tPoly {U φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    {x₀ : EuclSpace d} (hmin : IsLocalMin (fun y => U y - φ y) x₀)
    {η : ℝ} (hη : 0 < η) :
    IsLocalMin (fun y => U y - tPoly φ x₀ (-η) y) x₀ := by
  obtain ⟨δ, hδ, hT⟩ := exists_taylorErr_le hφ x₀ hη
  unfold IsLocalMin IsMinFilter at hmin ⊢
  filter_upwards [hmin, Metric.ball_mem_nhds x₀ hδ] with y hy hyb
  change U x₀ - φ x₀ ≤ U y - φ y at hy
  change U x₀ - tPoly φ x₀ (-η) x₀ ≤ U y - tPoly φ x₀ (-η) y
  have hz : ‖y - x₀‖ < δ := by rw [mem_ball, dist_eq_norm] at hyb; exact hyb
  have herr := (abs_le.1 (hT (y - x₀) hz)).1
  have hdec := decomp_at φ x₀ (y - x₀)
  have hxy : x₀ + (y - x₀) = y := by abel
  rw [hxy] at hdec
  rw [tPoly_self]
  simp only [tPoly]
  linarith

end

end PLaplacian
