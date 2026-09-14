/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.LineRestrict

/-!
# The second-order Taylor expansion: route and stubs

This file records the route to the second-order Peano expansion

  `φ (x + z) = φ x + Dφ x z + (1/2) D²φ x (z, z) + o(‖z‖²)`,

which Layer 3 needs and which Mathlib does not provide directly. Nothing here
is proved yet; the file exists so that the next session starts from a plan
rather than a blank page.

## What Mathlib provides

A search established the following. Present:

* `HasFDerivAt.isLittleO`, the first-order Peano form.
* `ContDiff.ftaylorSeries`, giving `HasFTaylorSeriesUpTo n f (ftaylorSeries 𝕜 f)`
  for a `C^n` function.
* `HasFTaylorSeriesUpTo.hasFDerivAt`, relating the `1`-jet to `fderiv` through
  `continuousMultilinearCurryFin1`.
* **`iteratedFDeriv_two_apply`**:
  `(iteratedFDeriv 𝕜 2 f z) m = fderiv 𝕜 (fderiv 𝕜 f) z (m 0) (m 1)`.
* `Convex.norm_image_sub_le_of_norm_fderiv_le`, the mean value inequality.
* `taylor_mean_remainder_lagrange`, one-dimensional, with hypotheses in terms
  of `iteratedDerivWithin` on `uIcc`.

Absent under any obvious name: a second-order Peano form. We checked
`ContDiffAt.isBigO_sub`, `HasFDerivAt.isLittleO_sub` and
`ContDiffAt.hasFTaylorSeriesUpToOn`; none exists.

## Why `iteratedFDeriv_two_apply` is the decisive find

Our initial gap audit identified the `iteratedDeriv` against `iteratedFDeriv`
glue as the likely friction point of the whole development, on the grounds
that the formal multilinear series packaging of `HasFTaylorSeriesUpTo` would
have to be unwound by hand into `fderiv (fderiv f)`. It does not: at order two
the translation is a single Mathlib lemma, stated exactly as needed. That
turns the Taylor extraction from a research problem into an exercise.

## Two routes

**Route 1, through the jet.** Take `ContDiff.ftaylorSeries`, specialise to
`n = 2`, and unwind the `2`-jet with `iteratedFDeriv_two_apply`. The remainder
estimate then comes from the definition of `HasFTaylorSeriesUpTo`, whose
higher-order fields give exactly the approximation statement. This is the
direct route and is preferred.

**Route 2, through the derivative map.** Apply the first-order Peano form to
`fderiv φ`, which is differentiable with derivative `fderiv (fderiv φ)` by
`differentiable_fderiv` of `Plaplacian.LineRestrict`, obtaining

  `Dφ (x+z) = Dφ x + D²φ x z + o(‖z‖)`,

then integrate along the segment from `x` to `x+z` using the mean value
inequality. Avoids multilinear packaging, at the cost of a segment estimate.

**Fallback.** The average expansion of `average_expansion` below needs only an
`O(‖z‖³)` remainder, which for a `C³` function follows from the
one-dimensional Lagrange remainder along lines --- and
`Plaplacian.LineRestrict` already supplies the line machinery. The hypothesis
is slightly stronger than the `C²` of the literature, but the convergence
proof applies the expansion only to test functions, which may be taken as
smooth as desired. If routes 1 and 2 prove awkward, this is the pragmatic
choice.

## The targets

Stated here as `TODO`s so that the shape is fixed before the work starts.
-/

open Set Topology Filter Asymptotics

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-- **The second-order Peano expansion.** See the routes above.

`TODO`: prove. Route 1 is preferred. -/
theorem taylor_two (φ : EuclSpace d → ℝ) (hφ : ContDiff ℝ 2 φ)
    (x : EuclSpace d) :
    (fun z => φ (x + z) - φ x - fderiv ℝ φ x z
        - (1/2) * fderiv ℝ (fderiv ℝ φ) x z z)
      =o[𝓝 0] fun z => ‖z‖ ^ 2 := by
  sorry

/-- **The average expansion**, the first consumer of
`Plaplacian.BallMoments`. Taylor expand, average over the ball, and observe
that the constant term gives `φ x`, the linear term vanishes by the odd
moments (`integral_coord_ball_eq_zero`), and the quadratic term contributes
`ε² / (2 (d+2))` times the Laplacian by
`setAverage_sq_coord_unitBall` together with
`integral_mul_coord_ball_eq_zero` for the off-diagonal entries.

`TODO`: prove, after `taylor_two`. This is the step for which the moment
computations of Layer 0 were built. -/
theorem average_expansion (φ : EuclSpace d → ℝ) (hφ : ContDiff ℝ 2 φ)
    (x : EuclSpace d) :
    (fun ε : ℝ => (⨍ y in Metric.ball x ε, φ y) - φ x
        - ε ^ 2 / (2 * ((d : ℝ) + 2)) * laplacianOf (hess φ x))
      =o[𝓝[>] 0] fun ε : ℝ => ε ^ 2 := by
  sorry

/-! ## What comes after

The extreme-value expansion,

  `(1/2) (sup_{B ε x} φ + inf_{B ε x} φ)
      = φ x + (ε²/2) Δ^N_∞ φ x + o(ε²)`,

requires near-maximizers to be localised within `O(ε)` of `x + ε ν`, where
`ν = ∇φ x / |∇φ x|`. Nothing built so far bears on this directly, and it is
the step our own analysis identifies as the hardest in the project.

Then the singular set: the case `∇φ x = 0`, where the envelopes
`viscFLower` and `viscFUpper` of `Plaplacian.Viscosity` apply, and where the
expansion must be stated in terms of the extreme eigenvalues rather than the
infinity Laplacian.

Combining the three gives the asymptotic expansion of the step operator,

  `T_ε φ x = φ x + (ε² / (2 (p + d))) Δ^N_p φ x + o(ε²)`,

which is the analytic heart of the convergence theorem.
-/

end PLaplacian

end
