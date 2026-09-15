/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Taylor1D

/-!
# The second-order Taylor expansion in several variables

For a twice continuously differentiable function there is a point of the open
unit interval at which the Lagrange remainder is attained:

  phi (x + z) = phi x + Dphi x z + (1/2) D2phi (x + xi z) (z, z).

Mathlib does not provide this. Its several-variable Taylor API,
HasFTaylorSeriesUpTo, has exactly three fields -- zero_eq, fderiv and cont --
none of which is a remainder estimate. Only the one-dimensional
taylor_mean_remainder_lagrange supplies a remainder. The expansion is
therefore obtained by restriction to the line through x in direction z, using
the machinery built for the multivariate second-order necessary condition in
Plaplacian.LineRestrict.

The remainder is left in Lagrange form rather than converted to little-o of
norm z squared. For the intended consumer, the expansion of the average over
a ball, the explicit remainder is more useful, since integrating it against
the moment computations of Plaplacian.BallMoments is more direct than
manipulating a little-o under an integral sign.

## Main results

- deriv_restrict, deriv_deriv_restrict
- taylor_two_lagrange
-/

open Set Topology Filter

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The several-variable expansion

Apply `taylor_one_deriv` to `g t = φ (lineMap x z t)` and substitute the line
derivatives. The three terms become `φ x`, `Dφ x z`, and
`(1/2) D²φ (x + ξ z) (z, z)`.
-/

/-- The first derivative of the restriction, as a function. -/
theorem deriv_restrict {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x z : EuclSpace d) :
    deriv (fun s : ℝ => φ (lineMap x z s))
      = fun t => fderiv ℝ φ (lineMap x z t) z := by
  funext t
  exact (hasDerivAt_first hφ x z t).deriv

/-- The second derivative of the restriction, as a function. -/
theorem deriv_deriv_restrict {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x z : EuclSpace d) :
    deriv (deriv (fun s : ℝ => φ (lineMap x z s)))
      = fun t => fderiv ℝ (fderiv ℝ φ) (lineMap x z t) z z := by
  rw [deriv_restrict hφ]
  funext t
  exact (hasDerivAt_second_at hφ x z t).deriv

/-- **The several-variable expansion with Lagrange remainder.** -/
theorem taylor_two_lagrange {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x z : EuclSpace d) :
    ∃ ξ ∈ Ioo (0:ℝ) 1,
      φ (x + z) = φ x + fderiv ℝ φ x z
        + (1/2) * fderiv ℝ (fderiv ℝ φ) (x + ξ • z) z z := by
  obtain ⟨ξ, hξ, hres⟩ :=
    taylor_one_deriv (fun s : ℝ => φ (lineMap x z s))
      (contDiff_restrict hφ x z)
  refine ⟨ξ, hξ, ?_⟩
  rw [deriv_restrict hφ] at hres
  rw [(hasDerivAt_second_at hφ x z ξ).deriv] at hres
  simp only [lineMap] at hres
  simpa using hres

end

end PLaplacian
