/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Plaplacian.Domain
import Plaplacian.BallMoments

/-!
# Extreme values of the norm on a ball, and averages of low-order polynomials

The discrete comparison principle perturbs a competitor by the strictly concave
function `ψ x = R ^ 2 - ‖x‖ ^ 2`. Evaluating `T_ε ψ` requires two things:

* the supremum and infimum of `‖y‖` over `closedBall x ε`, computed here;
* the average of `‖y‖ ^ 2` and of `inner ℝ x y` over `ball x ε`, for which the
  moment results of `Plaplacian.BallMoments` are used.

## The two cases for the infimum

The supremum is always `‖x‖ + ε`, attained by moving radially outward. The
infimum splits: if `ε ≤ ‖x‖` the ball misses the origin and the infimum is
`‖x‖ - ε`, attained by moving radially inward; if `‖x‖ ≤ ε` the ball contains
the origin and the infimum is `0`. Both cases occur for a general domain.

## Main results

- `norm_le_of_mem_closedBall`, `le_norm_of_mem_closedBall`: the bounds.
- `isGreatest_norm_closedBall`: the supremum, with witness.
- `isLeast_norm_closedBall`, `isLeast_norm_closedBall_zero`: the infimum, in
  the two cases.
- `integral_inner_ball_eq_zero`: the linear term averages to zero over a
  centred ball, by the odd moments.
-/

open MeasureTheory Metric Set

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-! ### Bounds on the norm over a ball -/

lemma norm_le_of_mem_closedBall {x y : EuclSpace d} {ε : ℝ}
    (hy : y ∈ closedBall x ε) : ‖y‖ ≤ ‖x‖ + ε := by
  have hd : ‖y - x‖ ≤ ε := by
    rw [← dist_eq_norm]; exact Metric.mem_closedBall.1 hy
  have hyx : y = x + (y - x) := by abel
  calc ‖y‖ = ‖x + (y - x)‖ := by rw [← hyx]
    _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
    _ ≤ ‖x‖ + ε := by linarith

lemma le_norm_of_mem_closedBall {x y : EuclSpace d} {ε : ℝ}
    (hy : y ∈ closedBall x ε) : ‖x‖ - ε ≤ ‖y‖ := by
  have hd : ‖x - y‖ ≤ ε := by
    rw [← dist_eq_norm, dist_comm]; exact Metric.mem_closedBall.1 hy
  have := norm_sub_norm_le x y
  linarith

/-! ### The supremum -/

lemma radial_witness_mem {x : EuclSpace d} (hx : x ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) :
    ((1 + ε / ‖x‖) • x) ∈ closedBall x ε := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h : (1 + ε / ‖x‖) • x - x = (ε / ‖x‖) • x := by module
  rw [h, norm_smul]
  simp [hxn.ne', abs_of_nonneg hε]

lemma radial_witness_norm {x : EuclSpace d} (hx : x ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖(1 + ε / ‖x‖) • x‖ = ‖x‖ + ε := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [norm_smul]
  have h1 : (0:ℝ) ≤ 1 + ε / ‖x‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg h1]
  field_simp

/-- **The supremum of the norm over a ball is `‖x‖ + ε`.** -/
theorem isGreatest_norm_closedBall {x : EuclSpace d} (hx : x ≠ 0) {ε : ℝ}
    (hε : 0 ≤ ε) :
    IsGreatest ((fun y : EuclSpace d => ‖y‖) '' closedBall x ε) (‖x‖ + ε) := by
  refine ⟨⟨(1 + ε / ‖x‖) • x, radial_witness_mem hx hε,
    radial_witness_norm hx hε⟩, ?_⟩
  rintro a ⟨y, hy, rfl⟩
  exact norm_le_of_mem_closedBall hy

/-! ### The infimum, in two cases -/

lemma inward_witness_mem {x : EuclSpace d} (hx : x ≠ 0) {ε : ℝ} (hε : 0 ≤ ε) :
    ((1 - ε / ‖x‖) • x) ∈ closedBall x ε := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h : (1 - ε / ‖x‖) • x - x = (-(ε / ‖x‖)) • x := by module
  rw [h, norm_smul]
  simp [hxn.ne', abs_of_nonneg hε]

lemma inward_witness_norm {x : EuclSpace d} (hx : x ≠ 0) {ε : ℝ}
    (hle : ε ≤ ‖x‖) : ‖(1 - ε / ‖x‖) • x‖ = ‖x‖ - ε := by
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [norm_smul]
  have h1 : (0:ℝ) ≤ 1 - ε / ‖x‖ := by
    have : ε / ‖x‖ ≤ 1 := by rw [div_le_one hxn]; exact hle
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg h1]
  field_simp

/-- **The infimum when the ball misses the origin.** -/
theorem isLeast_norm_closedBall {x : EuclSpace d} (hx : x ≠ 0) {ε : ℝ}
    (hε : 0 ≤ ε) (hle : ε ≤ ‖x‖) :
    IsLeast ((fun y : EuclSpace d => ‖y‖) '' closedBall x ε) (‖x‖ - ε) := by
  refine ⟨⟨(1 - ε / ‖x‖) • x, inward_witness_mem hx hε,
    inward_witness_norm hx hle⟩, ?_⟩
  rintro a ⟨y, hy, rfl⟩
  exact le_norm_of_mem_closedBall hy

/-- **The infimum when the ball contains the origin.** -/
theorem isLeast_norm_closedBall_zero {x : EuclSpace d} {ε : ℝ}
    (hle : ‖x‖ ≤ ε) :
    IsLeast ((fun y : EuclSpace d => ‖y‖) '' closedBall x ε) 0 := by
  refine ⟨⟨0, ?_, by simp⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm]
    simpa using hle
  · rintro a ⟨y, hy, rfl⟩
    exact norm_nonneg y

/-! ### The linear term averages to zero -/

lemma inner_expand (x z : EuclSpace d) :
    inner ℝ x z = ∑ i, (x.ofLp i) * (z.ofLp i) := by
  rw [PiLp.inner_apply]
  simp [RCLike.inner_apply, mul_comm]

lemma integral_const_mul_coord_ball (x : EuclSpace d) (i : Fin d) (ε : ℝ) :
    (∫ z in ball (0 : EuclSpace d) ε, (x.ofLp i) * (z.ofLp i)) = 0 := by
  rw [integral_const_mul, integral_coord_ball_eq_zero i ε, mul_zero]

lemma integrableOn_coord (i : Fin d) (ε : ℝ) :
    IntegrableOn (fun z : EuclSpace d => (z.ofLp i)) (ball (0 : EuclSpace d) ε) :=
  (ContinuousOn.integrableOn_compact (isCompact_closedBall _ _)
    (by fun_prop)).mono_set ball_subset_closedBall

lemma integrableOn_const_mul_coord (x : EuclSpace d) (i : Fin d) (ε : ℝ) :
    IntegrableOn (fun z : EuclSpace d => (x.ofLp i) * (z.ofLp i))
      (ball (0 : EuclSpace d) ε) :=
  (integrableOn_coord i ε).const_mul _

lemma integrableOn_normSq (ε : ℝ) :
    IntegrableOn (fun z : EuclSpace d => ‖z‖ ^ 2) (ball (0 : EuclSpace d) ε) :=
  (ContinuousOn.integrableOn_compact (isCompact_closedBall _ _)
    (by fun_prop)).mono_set ball_subset_closedBall

/-- **The linear term integrates to zero over a centred ball**, by the odd
moments of `Plaplacian.BallMoments`. -/
theorem integral_inner_ball_eq_zero (x : EuclSpace d) (ε : ℝ) :
    (∫ z in ball (0 : EuclSpace d) ε, inner ℝ x z) = (0 : ℝ) := by
  have h : (∫ z in ball (0 : EuclSpace d) ε, inner ℝ x z)
      = ∑ i : Fin d, ∫ z in ball (0 : EuclSpace d) ε,
          (x.ofLp i) * (z.ofLp i) := by
    rw [← MeasureTheory.integral_finsetSum Finset.univ
        fun i _ => integrableOn_const_mul_coord x i ε]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_ball fun z _ => ?_
    exact inner_expand x z
  rw [h, Finset.sum_congr rfl fun i _ => integral_const_mul_coord_ball x i ε]
  simp

lemma setAverage_normSq_nonneg {ε : ℝ} (hε : 0 < ε) :
    0 ≤ ⨍ z in ball (0 : EuclSpace d) ε, ‖z‖ ^ 2 := by
  have h0 : (⨍ _z in ball (0 : EuclSpace d) ε, (0 : ℝ)) = 0 :=
    setAverage_const_ball 0 0 hε
  rw [← h0]
  exact setAverage_mono_ball 0 integrableOn_const (integrableOn_normSq ε)
    (fun z => by positivity)

end PLaplacian
