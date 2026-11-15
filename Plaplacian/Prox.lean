/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.ConvexBasics

@[expose] public section

/-! # The proximal map

For `f` convex on the whole space,

  `J(y) = argmin_x ( f(x) + ½ ‖x - y‖² )`.

* **Existence**: the objective is coercive by the linear lower bound, so its
  sublevel set is compact and the minimum is attained there.
* **Uniqueness**: at the midpoint of two minimizers the convexity defect of
  `½‖·‖²` forces them to coincide.
* **The variational inequality**: `y - J(y)` is a subgradient of `f` at `J(y)`,
  by comparison with `J(y) + t(z - J(y))` as `t → 0`.
* **`J(x + p) = x`** for every subgradient `p` at `x`.
* **`J` is one-Lipschitz**: adding the subgradient inequalities at `J(y)` and
  `J(y')` gives `‖J y - J y'‖² ≤ ⟪y - y', J y - J y'⟫`.

The map is defined by Hilbert's choice operator, so that its definition needs
no hypothesis; its properties hold for convex `f`.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- The proximal objective. -/
def proxObj (f : EuclSpace d → ℝ) (y x : EuclSpace d) : ℝ := f x + 1 / 2 * ‖x - y‖ ^ 2

/-- **The proximal map.** -/
def proxMap (f : EuclSpace d → ℝ) (y : EuclSpace d) : EuclSpace d :=
  Classical.epsilon (fun x => ∀ z, proxObj f y x ≤ proxObj f y z)

/-- If `A ≤ B + t c` for all small `t > 0`, then `A ≤ B`. -/
theorem le_of_forall_small {A B c : ℝ} (hc : 0 ≤ c)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → A ≤ B + t * c) : A ≤ B := by
  by_contra hlt
  push Not at hlt
  have hAB : 0 < A - B := by linarith
  set t := min 1 ((A - B) / (2 * (c + 1))) with htdef
  have ht : 0 < t := lt_min one_pos (by positivity)
  have h1 := h t ht (min_le_left _ _)
  have ht2 : t ≤ (A - B) / (2 * (c + 1)) := min_le_right _ _
  have h2 : t * c ≤ (A - B) / 2 := by
    have e : (A - B) / (2 * (c + 1)) * c ≤ (A - B) / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    calc t * c ≤ (A - B) / (2 * (c + 1)) * c := mul_le_mul_of_nonneg_right ht2 hc
      _ ≤ (A - B) / 2 := e
  linarith

section prox

variable {f : EuclSpace d → ℝ}

/-- **The proximal objective attains its minimum.** -/
theorem prox_exists (hf : ConvexOn ℝ univ f) (y : EuclSpace d) :
    ∃ x, ∀ z, proxObj f y x ≤ proxObj f y z := by
  have hc := convex_continuous hf
  obtain ⟨C, hC0, hC⟩ := convex_lower_linear hf
  set V := proxObj f y y with hV
  set a := ‖y‖ with ha
  set B' := V - f 0 + C with hB'
  set R := 2 * |B'| + 2 * (a + C) + 1 with hR
  set K := {z : EuclSpace d | proxObj f y z ≤ V} with hK
  have hcont : Continuous (proxObj f y) := by unfold proxObj; fun_prop
  have hyK : y ∈ K := by rw [hK, Set.mem_ofPred_eq]
  -- the sublevel set is bounded
  have hKb : K ⊆ closedBall 0 R := by
    intro z hz
    have hz' : proxObj f y z ≤ V := hz
    rw [mem_closedBall_zero_iff]
    unfold proxObj at hz'
    set t := ‖z‖ with ht
    have ht0 : 0 ≤ t := norm_nonneg z
    have hrev : (t - a) ^ 2 ≤ ‖z - y‖ ^ 2 := by
      have h1 : |t - a| ≤ ‖z - y‖ := abs_norm_sub_norm_le z y
      have h2 : |t - a| ^ 2 ≤ ‖z - y‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rwa [sq_abs] at h2
    have hlow := hC z
    have hq : t ^ 2 ≤ 2 * B' + 2 * (a + C) * t := by nlinarith [sq_nonneg a]
    by_contra hbig
    push Not at hbig
    have ht1 : 1 ≤ t := by
      have : 0 ≤ 2 * |B'| + 2 * (a + C) := by
        have := abs_nonneg B'; have := norm_nonneg y; linarith
      linarith
    have hB : 2 * B' ≤ 2 * |B'| * t := by
      have := le_abs_self B'
      have h' : |B'| ≤ |B'| * t := le_mul_of_one_le_right (abs_nonneg _) ht1
      linarith
    have : t ^ 2 ≤ (2 * |B'| + 2 * (a + C)) * t := by nlinarith
    have : t ≤ 2 * |B'| + 2 * (a + C) := by
      by_contra h3; push Not at h3; nlinarith
    linarith
  have hKcl : IsClosed K := isClosed_le hcont continuous_const
  have hKc : IsCompact K :=
    Metric.isCompact_of_isClosed_isBounded hKcl (isBounded_closedBall.subset hKb)
  obtain ⟨x, hxK, hxmin⟩ := hKc.exists_isMinOn ⟨y, hyK⟩ hcont.continuousOn
  refine ⟨x, fun z => ?_⟩
  by_cases hz : z ∈ K
  · exact hxmin hz
  · have h1 : V < proxObj f y z := by
      by_contra h; push Not at h; exact hz h
    have h2 : proxObj f y x ≤ V := hxK
    linarith

theorem prox_min (hf : ConvexOn ℝ univ f) (y : EuclSpace d) :
    ∀ z, proxObj f y (proxMap f y) ≤ proxObj f y z :=
  Classical.epsilon_spec (prox_exists hf y)

/-- **The minimizer is unique.** -/
theorem prox_unique (hf : ConvexOn ℝ univ f) {y x₁ x₂ : EuclSpace d}
    (h₁ : ∀ z, proxObj f y x₁ ≤ proxObj f y z) (h₂ : ∀ z, proxObj f y x₂ ≤ proxObj f y z) :
    x₁ = x₂ := by
  set mid := (1 / 2 : ℝ) • x₁ + (1 / 2 : ℝ) • x₂ with hmid
  have hconv := hf.2 (mem_univ x₁) (mem_univ x₂) (by norm_num : (0:ℝ) ≤ 1 / 2)
    (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (1:ℝ) / 2 + 1 / 2 = 1)
  simp only [smul_eq_mul] at hconv
  have hsq := norm_sq_convex_comb (by norm_num : (1:ℝ) / 2 + 1 / 2 = 1) (x₁ - y) (x₂ - y)
  have e1 : (1 / 2 : ℝ) • (x₁ - y) + (1 / 2 : ℝ) • (x₂ - y) = mid - y := by
    rw [hmid, smul_sub, smul_sub]; module
  have e2 : x₁ - y - (x₂ - y) = x₁ - x₂ := by abel
  rw [e1, e2] at hsq
  have hm1 := h₁ mid
  have h12 := h₁ x₂
  have h21 := h₂ x₁
  unfold proxObj at hm1 h12 h21
  have hn : ‖x₁ - x₂‖ ^ 2 ≤ 0 := by nlinarith
  have hn0 : ‖x₁ - x₂‖ = 0 := by
    have := sq_nonneg ‖x₁ - x₂‖
    have h0 : ‖x₁ - x₂‖ ^ 2 = 0 := le_antisymm hn this
    exact (pow_eq_zero_iff (by norm_num)).1 h0
  exact sub_eq_zero.1 (norm_eq_zero.1 hn0)

/-- **The variational inequality**: `y - J y` is a subgradient at `J y`. -/
theorem prox_subgrad (hf : ConvexOn ℝ univ f) (y : EuclSpace d) :
    IsSubgrad f (proxMap f y) (y - proxMap f y) := by
  set x := proxMap f y with hx
  intro z
  apply le_of_forall_small (c := 1 / 2 * ‖z - x‖ ^ 2) (by positivity)
  intro t ht0 ht1
  set xt := (1 - t) • x + t • z with hxt
  have hmin := prox_min hf y xt
  rw [← hx] at hmin
  unfold proxObj at hmin
  have hconv := hf.2 (mem_univ x) (mem_univ z) (by linarith : 0 ≤ 1 - t) ht0.le
    (by ring : 1 - t + t = 1)
  simp only [smul_eq_mul] at hconv
  have e1 : xt - y = (x - y) + t • (z - x) := by rw [hxt]; module
  have hexp : ‖xt - y‖ ^ 2
      = ‖x - y‖ ^ 2 + 2 * t * inner ℝ (x - y) (z - x) + t ^ 2 * ‖z - x‖ ^ 2 := by
    rw [e1, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht0, mul_pow]
    ring
  rw [hexp] at hmin
  have hin : inner ℝ (y - x) (z - x) = -inner ℝ (x - y) (z - x) := by
    rw [← inner_neg_left, neg_sub]
  rw [hin]
  -- divide by t
  have key : t * (f x - inner ℝ (x - y) (z - x))
      ≤ t * (f z + t * (1 / 2 * ‖z - x‖ ^ 2)) := by nlinarith
  have := le_of_mul_le_mul_left key ht0
  linarith

/-- **`J(x + p) = x`** for every subgradient `p` at `x`. -/
theorem prox_of_subgrad (hf : ConvexOn ℝ univ f) {x p : EuclSpace d}
    (hp : IsSubgrad f x p) : proxMap f (x + p) = x := by
  have hxmin : ∀ z, proxObj f (x + p) x ≤ proxObj f (x + p) z := by
    intro z
    unfold proxObj
    have h1 := hp z
    have e1 : x - (x + p) = -p := by abel
    have e2 : z - (x + p) = (z - x) - p := by abel
    rw [e1, e2, norm_neg, norm_sub_sq_real]
    have : 0 ≤ ‖z - x‖ ^ 2 := sq_nonneg _
    have hc : inner ℝ (z - x) p = inner ℝ p (z - x) := real_inner_comm _ _
    nlinarith
  exact (prox_unique hf (prox_min hf (x + p)) hxmin)

/-- **The proximal map is one-Lipschitz.** -/
theorem prox_lipschitz (hf : ConvexOn ℝ univ f) : LipschitzWith 1 (proxMap f) := by
  apply LipschitzWith.of_dist_le_mul
  intro y y'
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  set x := proxMap f y
  set x' := proxMap f y'
  have h1 := prox_subgrad hf y x'
  have h2 := prox_subgrad hf y' x
  -- monotonicity
  have hmono : ‖x - x'‖ ^ 2 ≤ inner ℝ (y - y') (x - x') := by
    have e : inner ℝ (y - y') (x - x') - ‖x - x'‖ ^ 2
        = -(inner ℝ (y - x) (x' - x) + inner ℝ (y' - x') (x - x')) := by
      rw [← real_inner_self_eq_norm_sq]
      have a1 : x' - x = -(x - x') := by abel
      rw [a1, inner_neg_right]
      have a2 : y - y' = (y - x) - (y' - x') + (x - x') := by abel
      rw [a2, inner_add_left, inner_sub_left]
      ring
    linarith
  have hcs : inner ℝ (y - y') (x - x') ≤ ‖y - y'‖ * ‖x - x'‖ := real_inner_le_norm _ _
  by_cases h0 : ‖x - x'‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖x - x'‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have : ‖x - x'‖ * ‖x - x'‖ ≤ ‖y - y'‖ * ‖x - x'‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos

end prox

end

end PLaplacian
