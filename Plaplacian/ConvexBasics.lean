/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.SumsFinal

@[expose] public section

/-! # Convex functions and subgradients

The first file of the proof of Alexandrov's theorem. For `f` convex on the
whole space:

* `f` is continuous;
* `f` has a linear lower bound `f(x) ≥ f(0) - C(1 + ‖x‖)`, from compactness on
  the unit ball and convexity along rays, `f(x/‖x‖) ≤ (1 - t) f(0) + t f(x)`
  with `t = 1/‖x‖` --- this is the coercivity the proximal map needs;
* subgradients are locally bounded: if `m ≤ f ≤ M` on the ball of radius `2r`,
  every subgradient at a point of the ball of radius `r` has `r ‖p‖ ≤ M - m`;
* limits of subgradients are subgradients.

A subgradient of `f` at `x` is a `p` with `f(x) + ⟪p, z - x⟫ ≤ f(z)` for all
`z`. Their existence is proved later, from the proximal map, without the
Hahn--Banach theorem.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- **A subgradient.** -/
def IsSubgrad (f : EuclSpace d → ℝ) (x p : EuclSpace d) : Prop :=
  ∀ z, f x + inner ℝ p (z - x) ≤ f z

section basics

variable {f : EuclSpace d → ℝ}

/-- **A convex function on the whole space is continuous.** -/
theorem convex_continuous (hf : ConvexOn ℝ univ f) : Continuous f :=
  continuousOn_univ.1 (ConvexOn.continuousOn isOpen_univ hf)

/-- **The linear lower bound.** -/
theorem convex_lower_linear (hf : ConvexOn ℝ univ f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, f 0 - C * (1 + ‖x‖) ≤ f x := by
  have hc := convex_continuous hf
  obtain ⟨x₀, _, hmin⟩ := (isCompact_closedBall (0 : EuclSpace d) 1).exists_isMinOn
    ⟨0, by simp⟩ hc.continuousOn
  set m := f x₀ with hmdef
  set C := max 0 (f 0 - m) with hCdef
  have hC0 : 0 ≤ C := le_max_left _ _
  have hCm : f 0 - m ≤ C := le_max_right _ _
  refine ⟨C, hC0, fun x => ?_⟩
  by_cases hx : ‖x‖ ≤ 1
  · have h1 : m ≤ f x := hmin (mem_closedBall_zero_iff.2 hx)
    have h2 : 0 ≤ C * ‖x‖ := mul_nonneg hC0 (norm_nonneg x)
    nlinarith
  · push Not at hx
    have hn : ‖x‖ ≠ 0 := by linarith
    set t := ‖x‖⁻¹ with htdef
    have ht0 : 0 < t := inv_pos.2 (by linarith)
    have ht1 : t ≤ 1 := inv_le_one_of_one_le₀ hx.le
    -- the point on the unit sphere
    have hw : ‖t • x‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0, htdef, inv_mul_cancel₀ hn]
    have h1 : m ≤ f (t • x) := hmin (mem_closedBall_zero_iff.2 hw.le)
    -- convexity along the ray
    have h2 : f (t • x) ≤ (1 - t) * f 0 + t * f x := by
      have := hf.2 (mem_univ 0) (mem_univ x) (by linarith : 0 ≤ 1 - t) ht0.le
        (by ring : 1 - t + t = 1)
      simpa using this
    have e1 : ‖x‖ * ((1 - t) * f 0 + t * f x) = (‖x‖ - 1) * f 0 + f x := by
      rw [htdef]; field_simp
    have h3 : ‖x‖ * m ≤ (‖x‖ - 1) * f 0 + f x := by
      rw [← e1]; exact mul_le_mul_of_nonneg_left (h1.trans h2) (norm_nonneg x)
    have h4 : ‖x‖ * (f 0 - m) ≤ ‖x‖ * C := mul_le_mul_of_nonneg_left hCm (norm_nonneg x)
    nlinarith

/-- **A convex function is bounded above on closed balls.** -/
theorem convex_bdd_above_ball (hf : ConvexOn ℝ univ f) (x : EuclSpace d) (r : ℝ) :
    ∃ M, ∀ z ∈ closedBall x r, f z ≤ M := by
  by_cases hr : 0 ≤ r
  · obtain ⟨z₀, _, hmax⟩ := (isCompact_closedBall x r).exists_isMaxOn
      ⟨x, mem_closedBall_self hr⟩ (convex_continuous hf).continuousOn
    exact ⟨f z₀, fun z hz => hmax hz⟩
  · refine ⟨0, fun z hz => ?_⟩
    rw [mem_closedBall] at hz
    exfalso; linarith [dist_nonneg (x := z) (y := x)]

/-- **A convex function is bounded below on closed balls.** -/
theorem convex_bdd_below_ball (hf : ConvexOn ℝ univ f) (x : EuclSpace d) (r : ℝ) :
    ∃ m, ∀ z ∈ closedBall x r, m ≤ f z := by
  by_cases hr : 0 ≤ r
  · obtain ⟨z₀, _, hmin⟩ := (isCompact_closedBall x r).exists_isMinOn
      ⟨x, mem_closedBall_self hr⟩ (convex_continuous hf).continuousOn
    exact ⟨f z₀, fun z hz => hmin hz⟩
  · refine ⟨0, fun z hz => ?_⟩
    rw [mem_closedBall] at hz
    exfalso; linarith [dist_nonneg (x := z) (y := x)]

end basics

section subgrad

variable {f : EuclSpace d → ℝ}

/-- **Subgradients are locally bounded.** -/
theorem subgrad_norm_le {x z p : EuclSpace d} {r M m : ℝ} (hr : 0 < r)
    (hM : ∀ w ∈ closedBall x (2 * r), f w ≤ M)
    (hm : ∀ w ∈ closedBall x (2 * r), m ≤ f w)
    (hz : z ∈ closedBall x r) (hp : IsSubgrad f z p) :
    r * ‖p‖ ≤ M - m := by
  have hz2 : z ∈ closedBall x (2 * r) :=
    closedBall_subset_closedBall (by linarith) hz
  by_cases hp0 : p = 0
  · rw [hp0, norm_zero, mul_zero]
    have := hM z hz2
    have := hm z hz2
    linarith
  · have hpn : 0 < ‖p‖ := norm_pos_iff.2 hp0
    set e := (r / ‖p‖) • p with hedef
    have he : ‖e‖ = r := by
      rw [hedef, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hpn),
        div_mul_cancel₀ _ hpn.ne']
    have hze : z + e ∈ closedBall x (2 * r) := by
      rw [mem_closedBall, dist_eq_norm] at hz ⊢
      have : z + e - x = (z - x) + e := by abel
      rw [this]
      calc ‖(z - x) + e‖ ≤ ‖z - x‖ + ‖e‖ := norm_add_le _ _
        _ ≤ r + r := by rw [he]; linarith
        _ = 2 * r := by ring
    have h1 := hp (z + e)
    have e1 : z + e - z = e := by abel
    rw [e1, hedef, real_inner_smul_right, real_inner_self_eq_norm_sq] at h1
    have e2 : r / ‖p‖ * ‖p‖ ^ 2 = r * ‖p‖ := by field_simp
    rw [e2] at h1
    have := hM (z + e) hze
    have := hm z hz2
    linarith

/-- **Limits of subgradients are subgradients.** -/
theorem isSubgrad_of_tendsto (hc : Continuous f) {zs ps : ℕ → EuclSpace d}
    {z p : EuclSpace d} (hz : Tendsto zs atTop (𝓝 z)) (hp : Tendsto ps atTop (𝓝 p))
    (h : ∀ n, IsSubgrad f (zs n) (ps n)) : IsSubgrad f z p := by
  intro w
  have h1 : Tendsto (fun n => f (zs n)) atTop (𝓝 (f z)) := (hc.tendsto z).comp hz
  have h2 : Tendsto (fun n => inner ℝ (ps n) (w - zs n)) atTop (𝓝 (inner ℝ p (w - z))) :=
    hp.inner (tendsto_const_nhds.sub hz)
  exact le_of_tendsto_of_tendsto (h1.add h2) tendsto_const_nhds
    (Eventually.of_forall fun n => h n w)

end subgrad

end

end PLaplacian
