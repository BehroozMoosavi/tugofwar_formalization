/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

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

/-! ### Diagonal second moments

No reflection helps here: `z i ^ 2` is even under every sign flip. Instead we
sum over coordinates, use `∑ i, z i ^ 2 = ‖z‖ ^ 2`, compute the resulting radial
integral with `integral_fun_norm_addHaar`, and divide by `d` using the
coordinate symmetry supplied by `LinearIsometryEquiv.piLpCongrLeft`.

The constant `1 / (d + 2)` originates in `integral_radial_sq` below.
-/

namespace Diagonal

/-- Exponent arithmetic. `d - 1` is truncated natural subtraction, so this
genuinely needs `0 < d` and cannot be closed by `ring`. -/
lemma pow_sub_one_mul_sq {d : ℕ} (hd : 0 < d) (y : ℝ) :
    y ^ (d - 1) * y ^ 2 = y ^ (d + 1) := by
  rw [← pow_add]
  congr 1
  omega

/-- Folding the radial weight into the cut-off indicator. -/
lemma smul_indicator_sq {d : ℕ} (hd : 0 < d) (y : ℝ) :
    y ^ (d - 1) • Set.indicator (Set.Iio (1:ℝ)) (fun t : ℝ => t ^ 2) y
      = Set.indicator (Set.Iio (1:ℝ)) (fun t : ℝ => t ^ (d + 1)) y := by
  by_cases h : y ∈ Set.Iio (1:ℝ)
  · simp only [Set.indicator_of_mem h, smul_eq_mul]
    exact pow_sub_one_mul_sq hd y
  · simp only [Set.indicator_of_notMem h, smul_zero]

/-- The one-dimensional value `∫_0^1 y ^ n dy = 1 / (n + 1)`, written with the
cut-off as an indicator over `Ioi 0` --- the exact shape that
`MeasureTheory.integral_fun_norm_addHaar` produces. -/
lemma integral_Ioi_indicator_pow (n : ℕ) :
    (∫ y in Set.Ioi (0:ℝ),
        Set.indicator (Set.Iio (1:ℝ)) (fun t : ℝ => t ^ n) y)
      = 1 / (n + 1 : ℝ) := by
  rw [MeasureTheory.setIntegral_indicator measurableSet_Iio,
      Set.Ioi_inter_Iio,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      integral_pow]
  simp

/-- **The radial integral behind the constant `1 / (d + 2)`.** -/
theorem integral_radial_sq {d : ℕ} (hd : 0 < d) :
    (∫ y in Set.Ioi (0:ℝ), y ^ (d - 1) •
        Set.indicator (Set.Iio (1:ℝ)) (fun t : ℝ => t ^ 2) y)
      = 1 / (d + 2 : ℝ) := by
  rw [funext (smul_indicator_sq hd), integral_Ioi_indicator_pow]
  push_cast
  ring

end Diagonal

/-! ### Diagonal second moments: the coordinate symmetry and the constant

The pieces are assembled here into the statement of the paper:
`⨍_{B₁} z i ^ 2 = 1 / (d + 2)`.
-/

namespace Diagonal

variable {d : ℕ}

lemma integrableOn_sq_coord (i : Fin d) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun z : EuclSpaceM d => (z.ofLp i) ^ 2)
      (Metric.ball (0 : EuclSpaceM d) r) :=
  (ContinuousOn.integrableOn_compact (isCompact_closedBall _ _)
    (by fun_prop)).mono_set Metric.ball_subset_closedBall

lemma sum_sq_coord (z : EuclSpaceM d) : ∑ i, (z.ofLp i) ^ 2 = ‖z‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [sq_abs]

lemma integral_sum_sq_coord (r : ℝ) :
    (∫ z in Metric.ball (0 : EuclSpaceM d) r, ‖z‖ ^ 2)
      = ∑ i : Fin d, ∫ z in Metric.ball (0 : EuclSpaceM d) r, (z.ofLp i) ^ 2 := by
  rw [← MeasureTheory.integral_finsetSum Finset.univ
        fun i _ => integrableOn_sq_coord i r]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_ball fun z _ => ?_
  exact (sum_sq_coord z).symm

/-- Coordinate permutation as a linear isometry. Unlike `flipCoordEquiv`, this
comes free from `LinearIsometryEquiv.piLpCongrLeft`. -/
noncomputable def permEquiv (σ : Equiv.Perm (Fin d)) :
    EuclSpaceM d ≃ₗᵢ[ℝ] EuclSpaceM d :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ

lemma measurePreserving_perm (σ : Equiv.Perm (Fin d)) :
    MeasureTheory.MeasurePreserving (permEquiv (d := d) σ) volume volume :=
  LinearIsometryEquiv.measurePreserving _

@[simp] lemma permEquiv_apply (σ : Equiv.Perm (Fin d)) (z : EuclSpaceM d)
    (i : Fin d) : (permEquiv σ z).ofLp i = z.ofLp (σ.symm i) := by
  simp [permEquiv, LinearIsometryEquiv.piLpCongrLeft]

lemma measurableEmbedding_perm (σ : Equiv.Perm (Fin d)) :
    MeasurableEmbedding (permEquiv (d := d) σ) :=
  (permEquiv (d := d) σ).toHomeomorph.measurableEmbedding

/-- All coordinates have the same second moment, by the swap permutation. -/
lemma integral_sq_coord_eq (i j : Fin d) (r : ℝ) :
    (∫ z in Metric.ball (0 : EuclSpaceM d) r, (z.ofLp i) ^ 2)
      = ∫ z in Metric.ball (0 : EuclSpaceM d) r, (z.ofLp j) ^ 2 := by
  have hpre : (permEquiv (d := d) (Equiv.swap i j)) ⁻¹'
      (Metric.ball (0 : EuclSpaceM d) r) = Metric.ball (0 : EuclSpaceM d) r := by
    ext z; simp [Metric.mem_ball, dist_zero_right]
  have key := (measurePreserving_perm (Equiv.swap i j)).setIntegral_preimage_emb
    (measurableEmbedding_perm _)
    (fun w : EuclSpaceM d => (w.ofLp i) ^ 2)
    (Metric.ball (0 : EuclSpaceM d) r)
  rw [hpre] at key
  rw [← key]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_ball fun z _ => ?_
  simp [Equiv.swap_apply_def]

/-- The sum collapses: `∫ ‖z‖ ^ 2 = d * ∫ z i ^ 2`. -/
theorem integral_normSq_eq_nsmul (i : Fin d) (r : ℝ) :
    (∫ z in Metric.ball (0 : EuclSpaceM d) r, ‖z‖ ^ 2)
      = (d : ℝ) * ∫ z in Metric.ball (0 : EuclSpaceM d) r, (z.ofLp i) ^ 2 := by
  rw [integral_sum_sq_coord,
      Finset.sum_congr rfl fun j _ => integral_sq_coord_eq j i r]
  simp [Finset.sum_const, Finset.card_univ]

/-! #### The radial side -/

lemma mem_unitBall_iff (z : EuclSpaceM d) :
    z ∈ Metric.ball (0 : EuclSpaceM d) 1 ↔ ‖z‖ < 1 := by
  simp [Metric.mem_ball, dist_zero_right]

lemma integral_ball_eq_integral_indicator (g : ℝ → ℝ) :
    (∫ z in Metric.ball (0 : EuclSpaceM d) 1, g ‖z‖)
      = ∫ z : EuclSpaceM d, Set.indicator (Set.Iio (1:ℝ)) g ‖z‖ := by
  rw [← MeasureTheory.integral_indicator measurableSet_ball]
  refine MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun z => ?_)
  by_cases h : ‖z‖ < 1
  · simp [Set.indicator_of_mem, (mem_unitBall_iff z).2 h, h]
  · simp [Set.indicator_of_notMem, h]

/-- The radial computation on the unit ball. -/
theorem integral_normSq_unitBall [Nontrivial (EuclSpaceM d)] (hd : 0 < d) :
    (∫ z in Metric.ball (0 : EuclSpaceM d) 1, ‖z‖ ^ 2)
      = (d : ℝ) * (volume.real (Metric.ball (0 : EuclSpaceM d) 1))
          * (1 / (d + 2 : ℝ)) := by
  rw [integral_ball_eq_integral_indicator (fun t : ℝ => t ^ 2),
      MeasureTheory.integral_fun_norm_addHaar volume
        (Set.indicator (Set.Iio (1:ℝ)) (fun t : ℝ => t ^ 2)),
      finrank_euclideanSpace_fin, integral_radial_sq hd]
  simp [nsmul_eq_mul, smul_eq_mul]
  ring

/-! #### Cancellation -/

lemma volumeReal_unitBall_pos [Nontrivial (EuclSpaceM d)] :
    0 < volume.real (Metric.ball (0 : EuclSpaceM d) 1) := by
  have h1 : volume (Metric.ball (0 : EuclSpaceM d) 1) ≠ 0 :=
    (measure_ball_pos volume 0 one_pos).ne'
  have h2 : volume (Metric.ball (0 : EuclSpaceM d) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  simp only [MeasureTheory.Measure.real]
  exact ENNReal.toReal_pos h1 h2

theorem integral_sq_coord_unitBall [Nontrivial (EuclSpaceM d)] (hd : 0 < d)
    (i : Fin d) :
    (∫ z in Metric.ball (0 : EuclSpaceM d) 1, (z.ofLp i) ^ 2)
      = volume.real (Metric.ball (0 : EuclSpaceM d) 1) / (d + 2 : ℝ) := by
  have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have h := (integral_normSq_eq_nsmul i 1).symm.trans
    (integral_normSq_unitBall hd)
  field_simp at h ⊢
  linarith [h]

/-- **The diagonal second moment of the unit ball: the `1/(d+2)` of the
asymptotic expansion.** -/
theorem setAverage_sq_coord_unitBall [Nontrivial (EuclSpaceM d)] (hd : 0 < d)
    (i : Fin d) :
    (⨍ z in Metric.ball (0 : EuclSpaceM d) 1, (z.ofLp i) ^ 2)
      = 1 / (d + 2 : ℝ) := by
  rw [MeasureTheory.setAverage_eq, integral_sq_coord_unitBall hd i, smul_eq_mul]
  have hpos := volumeReal_unitBall_pos (d := d)
  field_simp

end Diagonal
