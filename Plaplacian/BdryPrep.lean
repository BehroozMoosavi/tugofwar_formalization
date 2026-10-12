/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.ExpCompact

/-! # Preparation for the boundary estimate

1. **Locality.** `T_ε` at `x` reads only values on `B_ε(x)`.
2. **Clamping.** The polynomial barrier is unbounded; clamped to `[-B, B]` it is
   bounded and measurable, and unchanged where `|v| ≤ B`.
3. **Apollonius.** For the midpoint `z` of `y₀` and `z₀`,
   `|x - z|² = (|x - z₀|² + |x - y₀|²)/2 - |y₀ - z₀|²/4`; so if `|y₀ - z₀| = δ₀` and
   `|x - z₀| ≥ δ₀ - e`, then `|x - z|² ≥ (δ₀/2)² + |x - y₀|²/2 - δ₀ e`. With `e = 0`
   this makes the contact with the smaller ball unique; with `e = ε` it reaches
   the strip outside `Ω`.
4. **Barrier bounds.** `ψ ≤ t`; `ψ ≥ -2a` when `-a ≤ t ≤ 1/(4M)` and `Ma ≤ 1`;
   `|ψ| ≤ |t| + M t²`.
-/

open Set Topology Filter Metric MeasureTheory

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-! ## Locality -/

/-- **The operator reads only values on the ball.** -/
theorem tugOfWarOp_congr_ball {p ε : ℝ} {v w : EuclSpace d → ℝ} {x : EuclSpace d}
    (h : ∀ y ∈ ball x ε, v y = w y) : tugOfWarOp p ε v x = tugOfWarOp p ε w x := by
  unfold tugOfWarOp
  rw [Set.image_congr h]
  have hae : (fun y => v y) =ᵐ[volume.restrict (ball x ε)] (fun y => w y) :=
    ae_restrict_of_forall_mem measurableSet_ball h
  rw [average_congr hae]

/-! ## Clamping -/

/-- **The clamp** of a function to `[-B, B]`. -/
def clampF (B : ℝ) (f : EuclSpace d → ℝ) : EuclSpace d → ℝ := fun x => max (min (f x) B) (-B)

theorem bddMeas_clampF {B : ℝ} (hB : 0 ≤ B) {f : EuclSpace d → ℝ} (hf : Continuous f) :
    BddMeas (clampF B f) := by
  refine ⟨((hf.min continuous_const).max continuous_const).measurable, ⟨B, fun y => ?_⟩⟩
  unfold clampF
  rw [abs_le]
  constructor
  · exact le_max_right _ _
  · exact max_le (min_le_right _ _) (by linarith)

theorem clampF_eq {B : ℝ} {f : EuclSpace d → ℝ} {x : EuclSpace d} (h : |f x| ≤ B) :
    clampF B f x = f x := by
  unfold clampF
  obtain ⟨h1, h2⟩ := abs_le.1 h
  rw [min_eq_left h2, max_eq_left h1]

/-! ## Apollonius -/

/-- The parallelogram identity in the form used for the midpoint. -/
theorem norm_sub_half_sq (a b : EuclSpace d) :
    ‖a - (1 / 2 : ℝ) • b‖ ^ 2 = (‖a‖ ^ 2 + ‖a - b‖ ^ 2) / 2 - ‖b‖ ^ 2 / 4 := by
  rw [norm_sub_sq_real a ((1 / 2 : ℝ) • b), norm_sub_sq_real a b, norm_smul,
    real_inner_smul_right, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  ring

/-- **Apollonius's identity** for the midpoint `z₀ + ½(y₀ - z₀)`. -/
theorem midpoint_sq (x y₀ z₀ : EuclSpace d) :
    ‖x - (z₀ + (1 / 2 : ℝ) • (y₀ - z₀))‖ ^ 2
      = (‖x - z₀‖ ^ 2 + ‖x - y₀‖ ^ 2) / 2 - ‖y₀ - z₀‖ ^ 2 / 4 := by
  have e1 : x - (z₀ + (1 / 2 : ℝ) • (y₀ - z₀)) = (x - z₀) - (1 / 2 : ℝ) • (y₀ - z₀) := by
    abel
  have e2 : x - y₀ = (x - z₀) - (y₀ - z₀) := by abel
  rw [e1, e2]
  exact norm_sub_half_sq (x - z₀) (y₀ - z₀)

/-- **The distance to the midpoint, from outside the exterior ball.** -/
theorem apoll_ge {δ₀ : ℝ} (_hδ₀ : 0 < δ₀) {y₀ z₀ : EuclSpace d} (hy : ‖y₀ - z₀‖ = δ₀)
    {x : EuclSpace d} {e : ℝ} (_he : 0 ≤ e) (he' : e ≤ δ₀) (hx : δ₀ - e ≤ ‖x - z₀‖) :
    (δ₀ / 2) ^ 2 + ‖x - y₀‖ ^ 2 / 2 - δ₀ * e ≤ ‖x - (z₀ + (1 / 2 : ℝ) • (y₀ - z₀))‖ ^ 2 := by
  rw [midpoint_sq, hy]
  have h1 : (δ₀ - e) ^ 2 ≤ ‖x - z₀‖ ^ 2 := by
    rw [sq, sq]; exact mul_self_le_mul_self (by linarith) hx
  nlinarith [sq_nonneg e]

/-! ## Barrier bounds -/

theorem bpsi_le_t {M : ℝ} (hM : 0 ≤ M) (z : EuclSpace d) (δ : ℝ) (x : EuclSpace d) :
    bpsi z δ M x ≤ ‖x - z‖ ^ 2 - δ ^ 2 := by
  unfold bpsi
  have := mul_nonneg hM (sq_nonneg (‖x - z‖ ^ 2 - δ ^ 2))
  linarith

theorem bpsi_ge_neg {M : ℝ} (hM : 0 < M) (z : EuclSpace d) (δ : ℝ) {x : EuclSpace d}
    {a : ℝ} (ha : 0 ≤ a) (hMa : M * a ≤ 1) (h1 : -a ≤ ‖x - z‖ ^ 2 - δ ^ 2)
    (h2 : ‖x - z‖ ^ 2 - δ ^ 2 ≤ 1 / (4 * M)) : -(2 * a) ≤ bpsi z δ M x := by
  rcases le_or_gt 0 (‖x - z‖ ^ 2 - δ ^ 2) with ht | ht
  · have := bpsi_nonneg hM z (by linarith : δ ^ 2 ≤ ‖x - z‖ ^ 2) (by linarith)
    linarith
  · unfold bpsi
    set t := ‖x - z‖ ^ 2 - δ ^ 2 with htdef
    have hsq : t ^ 2 ≤ a ^ 2 := by nlinarith
    have k1 : M * t ^ 2 ≤ M * a ^ 2 := mul_le_mul_of_nonneg_left hsq hM.le
    have k2 : M * a ^ 2 ≤ a := by
      have := mul_le_mul_of_nonneg_right hMa ha
      nlinarith
    linarith

theorem abs_bpsi_le {M : ℝ} (hM : 0 ≤ M) (z : EuclSpace d) (δ : ℝ) (x : EuclSpace d) :
    |bpsi z δ M x| ≤ |‖x - z‖ ^ 2 - δ ^ 2| + M * (‖x - z‖ ^ 2 - δ ^ 2) ^ 2 := by
  unfold bpsi
  calc |(‖x - z‖ ^ 2 - δ ^ 2) - M * (‖x - z‖ ^ 2 - δ ^ 2) ^ 2|
      ≤ |‖x - z‖ ^ 2 - δ ^ 2| + |M * (‖x - z‖ ^ 2 - δ ^ 2) ^ 2| := abs_sub _ _
    _ = |‖x - z‖ ^ 2 - δ ^ 2| + M * (‖x - z‖ ^ 2 - δ ^ 2) ^ 2 := by
        rw [abs_of_nonneg (mul_nonneg hM (sq_nonneg _) :
          0 ≤ M * (‖x - z‖ ^ 2 - δ ^ 2) ^ 2)]

end

end PLaplacian
