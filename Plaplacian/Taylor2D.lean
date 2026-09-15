/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Taylor1D

/-!
# The second-order Taylor expansion in several variables

For a twice continuously differentiable `φ` and any `x` and `z` there is `ξ`
in the open unit interval with

  `φ (x + z) = φ x + Dφ x z + (1/2) D²φ (x + ξ z) (z, z)`.

Mathlib does not provide this. Its several-variable Taylor API,
`HasFTaylorSeriesUpTo`, has exactly three fields --- `zero_eq`, `fderiv` and
`cont` --- none of which is a remainder estimate: the structure asserts that a
tower of multilinear maps consists of the successive derivatives and is
continuous, and says nothing about approximation. Neither
`HasFTaylorSeriesUpToOn.approx` nor a second-order Peano form exists. Only the
one-dimensional `taylor_mean_remainder_lagrange` supplies a remainder.

The expansion is therefore obtained by restriction to the line through `x` in
direction `z`, using the machinery built for the multivariate second-order
necessary condition in `Plaplacian.LineRestrict`. That the prerequisite for
Layer 2 turned out to be the prerequisite for Layer 3 as well was not
anticipated: our initial gap audit expected the `iteratedDeriv` against
`iteratedFDeriv` translation to be the friction point of the whole
development, and in the event the same line reduction served both, with
`ContDiff.fderiv_right` and `iteratedFDeriv_two_apply` supplying the pieces we
had expected to build by hand.

## Lagrange rather than Peano

The remainder is left in Lagrange form rather than converted to `o(‖z‖²)`.
For the intended consumer --- the expansion of the average over a ball --- the
explicit remainder is more useful, since integrating it against the moment
computations of `Plaplacian.BallMoments` is more direct than manipulating a
little-o under an integral sign. The point `ξ` depends on the integration
variable, so the average expansion will bound the remainder using continuity
of the Hessian (`continuous_hess`) rather than integrating it termwise.

## Main results

- `deriv_restrict`, `deriv_deriv_restrict`: the derivatives of the
  restriction, as functions.
- `taylor_two_lagrange`
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
