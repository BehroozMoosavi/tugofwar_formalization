/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Taylor2D

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

end

end Radius

end PLaplacian
