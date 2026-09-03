/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib

/-!
# Moments of the uniform measure on a Euclidean ball

The second-order asymptotic expansion of the tug-of-war step operator requires
the moments of Lebesgue measure on a ball: the odd moments vanish, the
off-diagonal second moments vanish, and the diagonal second moments equal
`1 / (d + 2)`.

None of these appear to be in mathlib, so they are developed here. The tools
used are all available upstream:

- `MeasureTheory.integral_fun_norm_addHaar` reduces a radial integral over `E`
  to a one-dimensional integral: `∫ f ‖x‖ = d • |B₁| • ∫ r in Ioi 0, r ^ (d-1) • f r`.
- `Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular` gives neg-invariance
  of `volume` on `EuclideanSpace`.
- `MeasureTheory.integral_neg_eq_self` performs the reflection `z ↦ -z`.

## Main results

- `integral_coord_ball_eq_zero`: the odd moments `∫ z i` vanish.

## TODO

- Off-diagonal second moments, by reflecting a single coordinate.
- Diagonal second moments, via `∑ i, z i ^ 2 = ‖z‖ ^ 2` and the radial
  reduction.

## Implementation notes

`import Mathlib` is used while the file is under development; narrow it once the
required modules are known.
-/

open MeasureTheory Metric Set

noncomputable section

/-- The ambient Euclidean space. -/
abbrev EuclSpaceM (d : ℕ) := EuclideanSpace ℝ (Fin d)

namespace PLaplacian

/-- Reflection symmetry of the coordinate integral over a centred ball. -/
lemma integral_neg_coord_ball (d : ℕ) (i : Fin d) (r : ℝ) :
    (∫ z in ball (0 : EuclSpaceM d) r, (-z) i)
      = ∫ z in ball (0 : EuclSpaceM d) r, z i := by
  have hneg : (volume : Measure (EuclSpaceM d)).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular volume
  rw [← integral_indicator measurableSet_ball,
      ← integral_indicator measurableSet_ball]
  rw [← integral_neg_eq_self
      (fun z => (ball (0 : EuclSpaceM d) r).indicator (fun w => w i) z) volume]
  congr 1
  ext z
  simp only
  by_cases h : z ∈ ball (0 : EuclSpaceM d) r
  · simp [h, show (-z) ∈ ball (0 : EuclSpaceM d) r from by simpa using h]
  · simp [h, show (-z) ∉ ball (0 : EuclSpaceM d) r from by simpa using h]

/-- Linearity: negating the integrand negates the integral. -/
lemma integral_neg_coord_ball' (d : ℕ) (i : Fin d) (r : ℝ) :
    (∫ z in ball (0 : EuclSpaceM d) r, (-z) i)
      = -∫ z in ball (0 : EuclSpaceM d) r, z i := by
  simp only [PiLp.neg_apply]
  exact integral_neg _

/-- **The odd moments of a centred ball vanish.**

Proof: the reflection `z ↦ -z` preserves both the ball and Lebesgue measure, so
the integral equals itself; but the integrand is odd, so it also equals its own
negative. Hence it is zero. -/
theorem integral_coord_ball_eq_zero (d : ℕ) (i : Fin d) (r : ℝ) :
    (∫ z in ball (0 : EuclSpaceM d) r, z i) = 0 := by
  have h1 := integral_neg_coord_ball d i r
  have h2 := integral_neg_coord_ball' d i r
  linarith [h1, h2]

end PLaplacian
