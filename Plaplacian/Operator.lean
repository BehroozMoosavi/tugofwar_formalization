/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Plaplacian.Existence

@[expose] public section

/-!
# The normalized p-Laplacian as a second-order operator

The viscosity theory of a second-order equation is organised around a
generator `F (x, r, q, X)` taking a point, a value, a gradient and a Hessian.
This file expresses the normalized `p`-Laplacian

  `Delta^N_p u = Delta u + (p - 2) <D^2 u nu, nu>,   nu = grad u / |grad u|`

in that form, and proves the three properties the theory needs.

## The type of the Hessian argument

Two choices present themselves: a continuous bilinear map
`EuclSpace d ->L[R] EuclSpace d ->L[R] R`, or a matrix. We take the former,
because it is what `fderiv (fderiv f)` produces, so the operator composes with
Mathlib's calculus without a conversion at every use. The matrix form would
read closer to the classical formula but would need a bridge everywhere.

## The three properties

* `normPLapOf_smul`: homogeneity of degree one in the Hessian. This is what
  distinguishes the normalized operator from the variational `p`-Laplacian.

* `normPLapOf_smul_left`: invariance under positive scaling of the gradient.
  This is what makes the operator genuinely a function of the *direction*
  `grad u / |grad u|` rather than of the gradient, and hence well defined in
  the viscosity sense. Note that the proof splits on `q = 0`, which is the
  first appearance of the singular set on which the operator is undefined.

* Degenerate ellipticity: `viscF` is nonincreasing in the Hessian, with the
  Hessian ordered as a quadratic form. This is the structural hypothesis of
  viscosity theory; without it there is no comparison principle for the
  limiting equation.

## TODO

The singular set. The operator is undefined where the gradient vanishes, and
the viscosity definitions must say what happens there: via the semicontinuous
envelopes `F^*` and `F_*`, or by restricting test functions to those with
non-vanishing gradient at the contact point. The choice determines the shape of
every definition downstream and should be settled from the literature before
the sub- and supersolution predicates are written.
-/

open Metric Set

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-! ### The two constituents -/

/-- The Laplacian of a bilinear form: its trace, as a sum over the standard
orthonormal basis. -/
def laplacianOf (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) : ℝ :=
  ∑ i : Fin d, X (EuclideanSpace.single i (1 : ℝ))
    (EuclideanSpace.single i (1 : ℝ))

/-- The normalized infinity Laplacian: the bilinear form evaluated twice at the
unit vector in the direction of `q`. -/
def infLaplacianOf (q : EuclSpace d)
    (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) : ℝ :=
  X (‖q‖⁻¹ • q) (‖q‖⁻¹ • q)

/-- **The normalized `p`-Laplacian of a Hessian**, at a point with gradient
`q`. This is `Delta^N_p`, not the `F` of the viscosity convention; see
`viscF`. -/
def normPLapOf (p : ℝ) (q : EuclSpace d)
    (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) : ℝ :=
  laplacianOf X + (p - 2) * infLaplacianOf q X

/-- The operator in the viscosity convention, so that the equation reads
`F = 0` and subsolutions satisfy `F <= 0`. -/
def viscF (p : ℝ) (q : EuclSpace d)
    (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) : ℝ :=
  - normPLapOf p q X

/-! ### Sanity checks -/

/-- For a unit vector the infinity Laplacian is `X q q`. -/
lemma infLaplacianOf_of_norm_one {q : EuclSpace d} (hq : ‖q‖ = 1)
    (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) :
    infLaplacianOf q X = X q q := by
  unfold infLaplacianOf
  rw [hq]
  simp

/-- At `p = 2` the operator is the Laplacian. -/
lemma normPLapOf_two (q : EuclSpace d)
    (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) :
    normPLapOf 2 q X = laplacianOf X := by
  unfold normPLapOf
  simp

/-! ### Homogeneity in the Hessian -/

lemma laplacianOf_smul (c : ℝ) (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) :
    laplacianOf (c • X) = c * laplacianOf X := by
  unfold laplacianOf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

lemma infLaplacianOf_smul (c : ℝ) (q : EuclSpace d)
    (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) :
    infLaplacianOf q (c • X) = c * infLaplacianOf q X := by
  unfold infLaplacianOf
  simp
  ring

/-- **Homogeneity of degree one in the Hessian.** -/
theorem normPLapOf_smul (p c : ℝ) (q : EuclSpace d)
    (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) :
    normPLapOf p q (c • X) = c * normPLapOf p q X := by
  unfold normPLapOf
  rw [laplacianOf_smul, infLaplacianOf_smul]
  ring

/-! ### Invariance under scaling of the gradient -/

/-- **The operator depends on the gradient only through its direction.** -/
theorem infLaplacianOf_smul_left {c : ℝ} (hc : 0 < c) (q : EuclSpace d)
    (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) :
    infLaplacianOf (c • q) X = infLaplacianOf q X := by
  unfold infLaplacianOf
  have hnorm : ‖c • q‖ = c * ‖q‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  rw [hnorm]
  by_cases hq : q = 0
  · simp [hq]
  · have hqn : (0 : ℝ) < ‖q‖ := norm_pos_iff.2 hq
    have hkey : (c * ‖q‖)⁻¹ • (c • q) = ‖q‖⁻¹ • q := by
      rw [smul_smul]
      congr 1
      field_simp
    rw [hkey]

theorem normPLapOf_smul_left (p : ℝ) {c : ℝ} (hc : 0 < c) (q : EuclSpace d)
    (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) :
    normPLapOf p (c • q) X = normPLapOf p q X := by
  unfold normPLapOf
  rw [infLaplacianOf_smul_left hc]

/-! ### Degenerate ellipticity -/

/-- **Degenerate ellipticity.** `F` is nonincreasing in the Hessian, ordered as
a quadratic form. This is the structural hypothesis of viscosity theory. -/
theorem viscF_antitone (p : ℝ) (hp : 2 ≤ p) (q : EuclSpace d)
    (X Y : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ)
    (hXY : ∀ v : EuclSpace d, X v v ≤ Y v v) :
    viscF p q Y ≤ viscF p q X := by
  unfold viscF normPLapOf laplacianOf infLaplacianOf
  have h1 : ∑ i : Fin d, X (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ))
      ≤ ∑ i : Fin d, Y (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single i (1 : ℝ)) :=
    Finset.sum_le_sum fun i _ => hXY _
  have h2 : X (‖q‖⁻¹ • q) (‖q‖⁻¹ • q) ≤ Y (‖q‖⁻¹ • q) (‖q‖⁻¹ • q) :=
    hXY _
  nlinarith [h1, h2]

end PLaplacian

end
