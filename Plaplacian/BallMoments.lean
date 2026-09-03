/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib

/-!
# Moments of Lebesgue measure on a Euclidean ball

The second-order asymptotic expansion of the tug-of-war step operator needs the
moments of Lebesgue measure on a centred ball: odd moments vanish, off-diagonal
second moments vanish, and diagonal second moments equal `1 / (d + 2)`.

None of these are in mathlib, so they are developed here. The upstream tools
used are:

- `MeasureTheory.integral_fun_norm_addHaar`, reducing a radial integral over `E`
  to a one-dimensional integral.
- `Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular`, giving
  neg-invariance of `volume` on `EuclideanSpace`.
- `MeasureTheory.integral_neg_eq_self`, performing the reflection `z ↦ -z`.
- `LinearIsometryEquiv.measurePreserving`, giving that any linear isometry of
  Euclidean space preserves `volume`.

The odd moments use the global reflection `z ↦ -z`. The off-diagonal moments
cannot: negating every coordinate leaves `z i * z j` unchanged. They instead
need a *single*-coordinate flip, which is constructed here as `flipCoordEquiv`
and does not appear to exist upstream.

## Main results

- `integral_coord_ball_eq_zero`: the odd moments `∫ z i` vanish.
- `flipCoordEquiv`: single-coordinate sign flip as a linear isometry equivalence.
- `integral_mul_coord_ball_eq_zero`: off-diagonal second moments vanish.

## TODO

Diagonal second moments, via `∑ i, z i ^ 2 = ‖z‖ ^ 2` and the radial reduction.

## Implementation notes

`import Mathlib` while under development; narrow once the modules are settled.
-/

open MeasureTheory Metric Set

noncomputable section

abbrev EuclSpaceM (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

namespace PLaplacian

/-! ### Odd moments, via the global reflection -/

/-- Reflection symmetry of the coordinate integral over a centred ball. -/
lemma integral_neg_coord_ball (i : Fin d) (r : ℝ) :
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
lemma integral_neg_coord_ball' (i : Fin d) (r : ℝ) :
    (∫ z in ball (0 : EuclSpaceM d) r, (-z) i)
      = -∫ z in ball (0 : EuclSpaceM d) r, z i := by
  simp only [PiLp.neg_apply]
  exact integral_neg _

/-- **The odd moments of a centred ball vanish.** -/
theorem integral_coord_ball_eq_zero (i : Fin d) (r : ℝ) :
    (∫ z in ball (0 : EuclSpaceM d) r, z i) = 0 := by
  have h1 := integral_neg_coord_ball i r
  have h2 := integral_neg_coord_ball' i r
  linarith [h1, h2]

/-! ### The single-coordinate flip

Negating all coordinates fixes `z i * z j`, so the off-diagonal moments need a
reflection in one coordinate only. -/

/-- Flip the sign of the `i`-th coordinate. -/
def flipCoord (i : Fin d) (z : EuclSpaceM d) : EuclSpaceM d :=
  (WithLp.equiv 2 _).symm (fun j => if j = i then -(z.ofLp j) else z.ofLp j)

lemma flipCoord_apply (i : Fin d) (z : EuclSpaceM d) (j : Fin d) :
    (flipCoord i z).ofLp j = if j = i then -(z.ofLp j) else z.ofLp j := by
  simp [flipCoord]

lemma norm_flipCoord (i : Fin d) (z : EuclSpaceM d) : ‖flipCoord i z‖ = ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [flipCoord]
  by_cases h : j = i
  · simp [h]
  · simp [h]

lemma flipCoord_involutive (i : Fin d) :
    Function.Involutive (flipCoord (d := d) i) := by
  intro z; ext j; simp only [flipCoord_apply]
  by_cases h : j = i
  · simp [h]
  · simp [h]

lemma flipCoord_add (i : Fin d) (z w : EuclSpaceM d) :
    flipCoord i (z + w) = flipCoord i z + flipCoord i w := by
  ext j; simp only [flipCoord_apply, PiLp.add_apply]
  by_cases h : j = i
  · simp [h]; ring
  · simp [h]

lemma flipCoord_smul (i : Fin d) (c : ℝ) (z : EuclSpaceM d) :
    flipCoord i (c • z) = c • flipCoord i z := by
  ext j; simp only [flipCoord_apply, PiLp.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · simp [h]
  · simp [h]

/-- The single-coordinate flip as a linear isometry equivalence. Being an
isometry, it preserves `volume` by `LinearIsometryEquiv.measurePreserving`. -/
def flipCoordEquiv (i : Fin d) : EuclSpaceM d ≃ₗᵢ[ℝ] EuclSpaceM d where
  toFun := flipCoord i
  invFun := flipCoord i
  left_inv := flipCoord_involutive i
  right_inv := flipCoord_involutive i
  map_add' := flipCoord_add i
  map_smul' := flipCoord_smul i
  norm_map' := norm_flipCoord i

lemma measurePreserving_flipCoord (i : Fin d) :
    MeasurePreserving (flipCoordEquiv (d := d) i) volume volume :=
  LinearIsometryEquiv.measurePreserving _

/-- The flip preserves the centred ball. -/
lemma flipCoord_mem_ball (i : Fin d) (r : ℝ) (z : EuclSpaceM d) :
    flipCoord i z ∈ ball (0 : EuclSpaceM d) r ↔
      z ∈ ball (0 : EuclSpaceM d) r := by
  simp [mem_ball, dist_zero_right, norm_flipCoord]

/-- The product of two distinct coordinates is odd under the flip. -/
lemma flip_mul_coord (i j : Fin d) (hij : i ≠ j) (z : EuclSpaceM d) :
    (flipCoord i z).ofLp i * (flipCoord i z).ofLp j
      = -(z.ofLp i * z.ofLp j) := by
  simp only [flipCoord_apply]
  simp [Ne.symm hij]

end PLaplacian
