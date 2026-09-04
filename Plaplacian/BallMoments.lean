/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

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


/-! ### Off-diagonal second moments -/

/-- The flip is a measurable embedding, being a homeomorphism. -/
lemma measurableEmbedding_flipCoord (i : Fin d) :
    MeasurableEmbedding (flipCoordEquiv (d := d) i) :=
  (flipCoordEquiv (d := d) i).toHomeomorph.measurableEmbedding

/-- The bundled equivalence agrees with the bare function. -/
@[simp] lemma flipCoordEquiv_apply (i : Fin d) (z : EuclSpaceM d) :
    (flipCoordEquiv (d := d) i) z = flipCoord i z := rfl

/-- Change of variables under the flip: it preserves both `volume` and the
centred ball, so the integral is unchanged. -/
lemma integral_flip_mul_coord (i j : Fin d) (r : ℝ) :
    (∫ z in ball (0 : EuclSpaceM d) r,
        (flipCoord i z).ofLp i * (flipCoord i z).ofLp j)
      = ∫ z in ball (0 : EuclSpaceM d) r, z.ofLp i * z.ofLp j := by
  have hpre : (flipCoordEquiv (d := d) i) ⁻¹' (ball (0 : EuclSpaceM d) r)
      = ball (0 : EuclSpaceM d) r := by
    ext z; simp
  have key := (measurePreserving_flipCoord i).setIntegral_preimage_emb
    (measurableEmbedding_flipCoord i)
    (fun w : EuclSpaceM d => w.ofLp i * w.ofLp j)
    (ball (0 : EuclSpaceM d) r)
  rw [hpre] at key
  simpa using key

/-- Oddness: for `j ≠ i` the integrand changes sign under the flip. -/
lemma integral_flip_mul_coord_neg (i j : Fin d) (hij : i ≠ j) (r : ℝ) :
    (∫ z in ball (0 : EuclSpaceM d) r,
        (flipCoord i z).ofLp i * (flipCoord i z).ofLp j)
      = -∫ z in ball (0 : EuclSpaceM d) r, z.ofLp i * z.ofLp j := by
  rw [← integral_neg]
  refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
  exact flip_mul_coord i j hij z

/-- **The off-diagonal second moments of a centred ball vanish.**

Flipping the sign of the `i`-th coordinate preserves both Lebesgue measure and
the ball, but negates `z i * z j` when `j ≠ i`. Hence the integral equals its
own negative, so it is zero. -/
theorem integral_mul_coord_ball_eq_zero (i j : Fin d) (hij : i ≠ j) (r : ℝ) :
    (∫ z in ball (0 : EuclSpaceM d) r, z.ofLp i * z.ofLp j) = 0 := by
  have h1 := integral_flip_mul_coord i j r
  have h2 := integral_flip_mul_coord_neg i j hij r
  linarith [h1, h2]

end PLaplacian
