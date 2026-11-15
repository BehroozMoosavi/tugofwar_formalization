/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Taylor2D

@[expose] public section

/-!
# Second moments at arbitrary radius

The moment computations of Plaplacian.BallMoments are stated for the unit
ball, while the asymptotic expansion needs radius epsilon. The development
there is in fact radius-general everywhere except the one-dimensional cut-off,
which integrates a power over the interval from zero to one. This file redoes
that single computation with the cut-off at epsilon and propagates it through
the radial reduction.

No dilation or change of variables is needed. That was the first route we
considered, and it fails for an incidental reason: the set-scaling notation
does not elaborate without annotation, and the average form of the change of
variables does not exist in Mathlib. Redoing the radial integral is both
shorter and reuses the existing proof structure verbatim.

The declarations live in a namespace Radius rather than extending Diagonal,
because Diagonal in BallMoments sits at the root rather than inside
PLaplacian and so would need root qualification from here.

## Main results

- integral_radial_sq_eps: the radial integral at radius epsilon.
- integral_normSq_ball_eps: the squared norm integrated over a ball.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

namespace Radius

noncomputable section

variable {d : ℕ}

/-! ## The second moment at arbitrary radius

The unit-ball development of `Plaplacian.BallMoments` is radius-general
everywhere except the one-dimensional cut-off. This namespace redoes that one
computation at radius `ε` and propagates it.

Put in a fresh namespace `Radius` rather than reopening `Diagonal`, which
lives at the root rather than inside `PLaplacian` and so needs `_root_.`
qualification from here.
-/

/-- The one-dimensional value at radius `ε`. -/
lemma integral_Ioi_indicator_pow_eps (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    (∫ y in Set.Ioi (0:ℝ),
        Set.indicator (Set.Iio ε) (fun t : ℝ => t ^ n) y)
      = ε ^ (n + 1) / (n + 1 : ℝ) := by
  rw [MeasureTheory.setIntegral_indicator measurableSet_Iio,
      Set.Ioi_inter_Iio,
      ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hε.le,
      integral_pow]
  simp

lemma smul_indicator_sq_eps (hd : 0 < d) {ε : ℝ} (y : ℝ) :
    y ^ (d - 1) • Set.indicator (Set.Iio ε) (fun t : ℝ => t ^ 2) y
      = Set.indicator (Set.Iio ε) (fun t : ℝ => t ^ (d + 1)) y := by
  by_cases h : y ∈ Set.Iio ε
  · simp only [Set.indicator_of_mem h, smul_eq_mul]
    exact _root_.Diagonal.pow_sub_one_mul_sq hd y
  · simp only [Set.indicator_of_notMem h, smul_zero]

/-- **The radial integral at radius `ε`.** -/
theorem integral_radial_sq_eps (hd : 0 < d) {ε : ℝ} (hε : 0 < ε) :
    (∫ y in Set.Ioi (0:ℝ), y ^ (d - 1) •
        Set.indicator (Set.Iio ε) (fun t : ℝ => t ^ 2) y)
      = ε ^ (d + 2) / (d + 2 : ℝ) := by
  rw [funext (smul_indicator_sq_eps hd), integral_Ioi_indicator_pow_eps _ hε]
  push_cast
  ring

/-! ### Through the radial reduction

`integral_normSq_unitBall` in `BallMoments` restricts the squared norm to the
unit ball by writing it as an indicator and applying
`integral_fun_norm_addHaar`. The same step at radius `ε` uses the indicator
cutting off at `ε`, which `integral_radial_sq_eps` evaluates.
-/


/-- The squared norm on a ball, as an indicator integral over the space. -/
lemma setIntegral_normSq_eq_indicator {ε : ℝ} :
    (∫ z in Metric.ball (0 : EuclSpace d) ε, ‖z‖ ^ 2)
      = ∫ z : EuclSpace d,
          Set.indicator (Metric.ball (0 : EuclSpace d) ε)
            (fun w => ‖w‖ ^ 2) z := by
  rw [← MeasureTheory.integral_indicator measurableSet_ball]

/-- The indicator of a ball, as a function of the norm. -/
lemma indicator_ball_eq {ε : ℝ} (z : EuclSpace d) :
    Set.indicator (Metric.ball (0 : EuclSpace d) ε)
        (fun w => ‖w‖ ^ 2) z
      = Set.indicator (Set.Iio ε) (fun t : ℝ => t ^ 2) ‖z‖ := by
  by_cases h : ‖z‖ < ε
  · have hz : z ∈ Metric.ball (0 : EuclSpace d) ε := by
      simpa [Metric.mem_ball, dist_zero_right] using h
    rw [Set.indicator_of_mem hz, Set.indicator_of_mem (by exact h)]
  · have hz : z ∉ Metric.ball (0 : EuclSpace d) ε := by
      simpa [Metric.mem_ball, dist_zero_right] using h
    rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (by exact h)]

/-- **The squared-norm integral at radius `ε`.** -/
theorem integral_normSq_ball_eps [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ z in Metric.ball (0 : EuclSpace d) ε, ‖z‖ ^ 2)
      = d * volume.real (Metric.ball (0 : EuclSpace d) 1)
        * (ε ^ (d + 2) / (d + 2 : ℝ)) := by
  rw [setIntegral_normSq_eq_indicator]
  rw [funext (indicator_ball_eq (d := d) (ε := ε))]
  rw [MeasureTheory.integral_fun_norm_addHaar volume
        (fun t : ℝ => Set.indicator (Set.Iio ε) (fun s : ℝ => s ^ 2) t)]
  rw [finrank_euclideanSpace_fin, integral_radial_sq_eps hd hε]
  simp [mul_assoc]

/-! ## The coordinate moment at arbitrary radius

`Diagonal.integral_normSq_eq_nsmul` holds at arbitrary radius, so combining it
with `integral_normSq_ball_eps` gives the coordinate moment. Converting to an
average needs the ball volume, which scales as the `d`-th power of the radius,
so the unit-ball volume cancels and only `ε ^ 2` survives.
-/

/-- **The coordinate second moment at radius `ε`.** -/
theorem integral_sq_coord_ball_eps [Nontrivial (EuclSpace d)] (hd : 0 < d)
    (i : Fin d) {ε : ℝ} (hε : 0 < ε) :
    (∫ z in Metric.ball (0 : EuclSpace d) ε, (z.ofLp i) ^ 2)
      = volume.real (Metric.ball (0 : EuclSpace d) 1)
        * (ε ^ (d + 2) / (d + 2 : ℝ)) := by
  have hdne : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hsum := Diagonal.integral_normSq_eq_nsmul i ε
  have hnorm := integral_normSq_ball_eps hd hε
  rw [hnorm] at hsum
  field_simp at hsum ⊢
  linarith [hsum]

/-- The ball volume scales as the `d`-th power of the radius, in
`Measure.real` form. -/
theorem volumeReal_ball_eq [Nontrivial (EuclSpace d)] {ε : ℝ} (hε : 0 < ε) :
    volume.real (Metric.ball (0 : EuclSpace d) ε)
      = ε ^ d * volume.real (Metric.ball (0 : EuclSpace d) 1) := by
  have h := Measure.addHaar_ball_of_pos volume (0 : EuclSpace d) hε
  rw [finrank_euclideanSpace_fin] at h
  simp only [MeasureTheory.Measure.real]
  rw [h, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]

theorem volumeReal_unitBall_pos' [Nontrivial (EuclSpace d)] :
    (0 : ℝ) < volume.real (Metric.ball (0 : EuclSpace d) 1) := by
  have h1 : volume (Metric.ball (0 : EuclSpace d) 1) ≠ 0 :=
    measure_ball_ne_zero 0 (by norm_num)
  have h2 : volume (Metric.ball (0 : EuclSpace d) 1) ≠ ⊤ :=
    measure_ball_lt_top.ne
  simp only [MeasureTheory.Measure.real]
  exact ENNReal.toReal_pos h1 h2

/-- **The coordinate second moment as an average.** -/
theorem setAverage_sq_coord_ball_eps [Nontrivial (EuclSpace d)] (hd : 0 < d)
    (i : Fin d) {ε : ℝ} (hε : 0 < ε) :
    (⨍ z in Metric.ball (0 : EuclSpace d) ε, (z.ofLp i) ^ 2)
      = ε ^ 2 / ((d : ℝ) + 2) := by
  rw [MeasureTheory.setAverage_eq, integral_sq_coord_ball_eps hd i hε,
      volumeReal_ball_eq hε, smul_eq_mul]
  have hvol := volumeReal_unitBall_pos' (d := d)
  have hεd : (0 : ℝ) < ε ^ d := by positivity
  have hd2 : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  field_simp
  ring

end

end Radius

end PLaplacian
