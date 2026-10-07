/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Prox

/-! # Subgradients exist everywhere

A convex function on the whole space has a subgradient at every point. The
proof uses the proximal map instead of the Hahn--Banach theorem.

For `λₙ = 1/(n + 1)`, let `zₙ` be the proximal point of `λₙ f` at `x`. The
variational inequality, divided by `λₙ`, makes `pₙ = λₙ⁻¹ (x - zₙ)` a
subgradient of `f` at `zₙ`. Comparing the proximal objective with its value at
`x` gives `½ rₙ² ≤ λₙ (A + C rₙ)` for `rₙ = ‖zₙ - x‖`, hence
`rₙ ≤ 2λₙ(A + C) + √(2λₙ(A + C)) → 0`; so `zₙ → x`, eventually inside the unit
ball about `x`, where subgradients are bounded. A subsequence of the `pₙ`
converges, and its limit is a subgradient at `x`.

A chosen subgradient at each point is then defined by Hilbert's choice
operator, for the later files.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



section exist

variable {f : EuclSpace d → ℝ}

/-- A subgradient of `λ f`, divided by `λ`, is a subgradient of `f`. -/
theorem isSubgrad_of_smul {lam : ℝ} (hlam : 0 < lam) {z v : EuclSpace d}
    (h : IsSubgrad (fun w => lam • f w) z v) : IsSubgrad f z (lam⁻¹ • v) := by
  intro w
  have h1 := h w
  simp only [smul_eq_mul] at h1
  rw [real_inner_smul_left]
  have h2 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hlam.le)
  have e1 : lam⁻¹ * (lam * f z + inner ℝ v (w - z)) = f z + lam⁻¹ * inner ℝ v (w - z) := by
    field_simp
  have e2 : lam⁻¹ * (lam * f w) = f w := by field_simp
  linarith

/-- **The proximal points of `λ f` approach `x`.** -/
theorem prox_smul_dist (hf : ConvexOn ℝ univ f) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, f 0 - C * (1 + ‖x‖) ≤ f x) {lam : ℝ} (hlam : 0 < lam) (x : EuclSpace d) :
    ‖proxMap (fun w => lam • f w) x - x‖
      ≤ 2 * lam * ((f x - f 0 + C * (1 + ‖x‖)) + C)
        + Real.sqrt (2 * lam * ((f x - f 0 + C * (1 + ‖x‖)) + C)) := by
  set A := f x - f 0 + C * (1 + ‖x‖) with hA
  have hA0 : 0 ≤ A := by have := hC x; linarith
  set z := proxMap (fun w => lam • f w) x with hz
  have hmin := prox_min (hf.smul hlam.le) x x
  rw [← hz] at hmin
  unfold proxObj at hmin
  simp only [smul_eq_mul, sub_self, norm_zero] at hmin
  set r := ‖z - x‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  -- the lower bound at z
  have hlow := hC z
  have hzn : ‖z‖ ≤ ‖x‖ + r := by
    have : z = x + (z - x) := by abel
    calc ‖z‖ = ‖x + (z - x)‖ := by rw [← this]
      _ ≤ ‖x‖ + ‖z - x‖ := norm_add_le _ _
  have hfz : f x - f z ≤ A + C * r := by
    have := mul_le_mul_of_nonneg_left hzn hC0
    nlinarith
  have hq : r ^ 2 ≤ 2 * lam * (A + C * r) := by
    have := mul_le_mul_of_nonneg_left hfz hlam.le
    nlinarith
  have hs0 : 0 ≤ Real.sqrt (2 * lam * (A + C)) := Real.sqrt_nonneg _
  have hl0 : 0 ≤ 2 * lam * (A + C) := by positivity
  rcases le_or_gt r 1 with h1 | h1
  · -- r ≤ 1
    have h2 : r ^ 2 ≤ 2 * lam * (A + C) := by
      have : C * r ≤ C := by nlinarith
      nlinarith
    have h3 : r ≤ Real.sqrt (2 * lam * (A + C)) := by
      have := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq hr0] at this
    linarith
  · -- r > 1
    have h2 : r ^ 2 ≤ 2 * lam * (A + C) * r := by
      have : A ≤ A * r := le_mul_of_one_le_right hA0 h1.le
      nlinarith
    have h3 : r ≤ 2 * lam * (A + C) := by
      have hrpos : 0 < r := by linarith
      have : r * r ≤ 2 * lam * (A + C) * r := by nlinarith
      exact le_of_mul_le_mul_right this hrpos
    linarith

/-- **A convex function has a subgradient at every point.** -/
theorem subgrad_exists (hf : ConvexOn ℝ univ f) (x : EuclSpace d) :
    ∃ p, IsSubgrad f x p := by
  obtain ⟨C, hC0, hC⟩ := convex_lower_linear hf
  set A := f x - f 0 + C * (1 + ‖x‖) with hA
  have hA0 : 0 ≤ A := by have := hC x; linarith
  set lam : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hlamdef
  have hlam : ∀ n, 0 < lam n := fun n => by rw [hlamdef]; positivity
  set z : ℕ → EuclSpace d := fun n => proxMap (fun w => lam n • f w) x with hzdef
  set pp : ℕ → EuclSpace d := fun n => (lam n)⁻¹ • (x - z n) with hppdef
  have hsub : ∀ n, IsSubgrad f (z n) (pp n) := fun n =>
    isSubgrad_of_smul (hlam n) (prox_subgrad (hf.smul (hlam n).le) x)
  -- the proximal points converge to x
  have hlamT : Tendsto lam atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hbT : Tendsto (fun n => 2 * lam n * (A + C) + Real.sqrt (2 * lam n * (A + C)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => 2 * lam n * (A + C)) atTop (𝓝 (2 * 0 * (A + C))) :=
      (hlamT.const_mul 2).mul_const (A + C)
    rw [mul_zero, zero_mul] at h1
    have h2 : Tendsto (fun n => Real.sqrt (2 * lam n * (A + C))) atTop (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at h2
    have := h1.add h2
    rwa [add_zero] at this
  have hzT : Tendsto z atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _)
      (fun n => prox_smul_dist hf hC0 hC (hlam n) x) hbT
  -- the subgradients are eventually bounded
  obtain ⟨M, hM⟩ := convex_bdd_above_ball hf x (2 * 1)
  obtain ⟨m, hm⟩ := convex_bdd_below_ball hf x (2 * 1)
  have hev : ∀ᶠ n in atTop, z n ∈ closedBall x 1 := hzT (closedBall_mem_nhds x one_pos)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have hpb : ∀ n, ‖pp (n + N)‖ ≤ M - m := fun n => by
    have := subgrad_norm_le one_pos hM hm (hN (n + N) (by omega)) (hsub (n + N))
    linarith
  -- a convergent subsequence, whose limit is a subgradient at x
  obtain ⟨p, _, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded (isBounded_closedBall (x := (0 : EuclSpace d)) (r := M - m))
      (fun n => mem_closedBall_zero_iff.2 (hpb n))
  have hidx : Tendsto (fun n => φ n + N) atTop atTop :=
    (tendsto_add_atTop_nat N).comp hφ.tendsto_atTop
  exact ⟨p, isSubgrad_of_tendsto (convex_continuous hf)
    (zs := fun n => z (φ n + N)) (ps := fun n => pp (φ n + N))
    (hzT.comp hidx) hlim (fun n => hsub _)⟩

end exist

/-- **A chosen subgradient** at each point. -/
def subgradSel (f : EuclSpace d → ℝ) (x : EuclSpace d) : EuclSpace d :=
  Classical.epsilon (IsSubgrad f x)

theorem subgradSel_spec {f : EuclSpace d → ℝ} (hf : ConvexOn ℝ univ f) (x : EuclSpace d) :
    IsSubgrad f x (subgradSel f x) :=
  Classical.epsilon_spec (subgrad_exists hf x)

/-- **The proximal map is onto**: every point is the proximal point of itself
plus a subgradient. -/
theorem prox_surj {f : EuclSpace d → ℝ} (hf : ConvexOn ℝ univ f) (x : EuclSpace d) :
    proxMap f (x + subgradSel f x) = x :=
  prox_of_subgrad hf (subgradSel_spec hf x)

end

end PLaplacian
