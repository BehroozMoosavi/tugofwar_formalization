/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.SumsSplit

/-! # Jet algebra

Three facts about jets used throughout the proof of the theorem of sums.

* **Linear shifts.** Subtracting a linear function `⟪a, ·⟫` shifts the
  gradient of every jet by `a` and leaves the form unchanged; the same holds
  for closed jets. This lets the gradient of the penalty be absorbed into the
  functions, reducing to a penalty with vanishing gradient.

* **The second-order condition at a maximum.** If `f` has a local maximum at
  `x` and `(q, X)` is a subjet there, then `q = 0` and `X ≤ 0`.

* **The semiconvex Hessian bound.** If `w + (λ/2)‖·‖²` is convex and `(q, X)`
  is a superjet of `w`, then `X(v,v) ≥ -λ‖v‖²`. Convexity along the segment
  through `x ± t v` and the parallelogram law cancel the linear terms.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



section shift

variable {u : EuclSpace d → ℝ} {x q a : EuclSpace d} {X : Bilin d}

/-- Subtracting a linear function shifts a superjet's gradient. -/
theorem superJet_sub_linear (h : (q, X) ∈ SuperJet u x) :
    (q - a, X) ∈ SuperJet (fun y => u y - inner ℝ a y) x := by
  intro η hη
  filter_upwards [h η hη] with y hy
  change u y ≤ u x + inner ℝ q (y - x) + (1 / 2) * (X (y - x)) (y - x)
    + η * ‖y - x‖ ^ 2 at hy
  change u y - inner ℝ a y ≤ u x - inner ℝ a x + inner ℝ (q - a) (y - x)
    + (1 / 2) * (X (y - x)) (y - x) + η * ‖y - x‖ ^ 2
  have h1 : inner ℝ (q - a) (y - x) = inner ℝ q (y - x) - inner ℝ a (y - x) :=
    inner_sub_left _ _ _
  have h2 : inner ℝ a (y - x) = inner ℝ a y - inner ℝ a x := inner_sub_right _ _ _
  linarith

/-- And back: adding the linear function restores it. -/
theorem superJet_of_sub_linear
    (h : (q, X) ∈ SuperJet (fun y => u y - inner ℝ a y) x) :
    (q + a, X) ∈ SuperJet u x := by
  intro η hη
  filter_upwards [h η hη] with y hy
  change u y - inner ℝ a y ≤ u x - inner ℝ a x + inner ℝ q (y - x)
    + (1 / 2) * (X (y - x)) (y - x) + η * ‖y - x‖ ^ 2 at hy
  change u y ≤ u x + inner ℝ (q + a) (y - x) + (1 / 2) * (X (y - x)) (y - x)
    + η * ‖y - x‖ ^ 2
  have h1 : inner ℝ (q + a) (y - x) = inner ℝ q (y - x) + inner ℝ a (y - x) :=
    inner_add_left _ _ _
  have h2 : inner ℝ a (y - x) = inner ℝ a y - inner ℝ a x := inner_sub_right _ _ _
  linarith

/-- Subtracting a linear function shifts a subjet's gradient back. -/
theorem subJet_of_sub_linear
    (h : (q, X) ∈ SubJet (fun y => u y - inner ℝ a y) x) :
    (q + a, X) ∈ SubJet u x := by
  intro η hη
  filter_upwards [h η hη] with y hy
  change u x - inner ℝ a x + inner ℝ q (y - x) + (1 / 2) * (X (y - x)) (y - x)
    - η * ‖y - x‖ ^ 2 ≤ u y - inner ℝ a y at hy
  change u x + inner ℝ (q + a) (y - x) + (1 / 2) * (X (y - x)) (y - x)
    - η * ‖y - x‖ ^ 2 ≤ u y
  have h1 : inner ℝ (q + a) (y - x) = inner ℝ q (y - x) + inner ℝ a (y - x) :=
    inner_add_left _ _ _
  have h2 : inner ℝ a (y - x) = inner ℝ a y - inner ℝ a x := inner_sub_right _ _ _
  linarith

/-- **Closed superjets shift back.** -/
theorem clSuperJet_of_sub_linear
    (h : (q, X) ∈ ClSuperJet (fun y => u y - inner ℝ a y) x) :
    (q + a, X) ∈ ClSuperJet u x := by
  obtain ⟨xs, qs, Xs, hj, hxs, hus, hqs, hXs⟩ := h
  refine ⟨xs, fun n => qs n + a, Xs, fun n => superJet_of_sub_linear (hj n),
    hxs, ?_, hqs.add tendsto_const_nhds, hXs⟩
  have hlin : Tendsto (fun n => inner ℝ a (xs n)) atTop (𝓝 (inner ℝ a x)) :=
    ((continuous_const.inner continuous_id).tendsto x).comp hxs
  have := hus.add hlin
  simpa using this

/-- **Closed subjets shift back.** -/
theorem clSubJet_of_sub_linear
    (h : (q, X) ∈ ClSubJet (fun y => u y - inner ℝ a y) x) :
    (q + a, X) ∈ ClSubJet u x := by
  obtain ⟨xs, qs, Xs, hj, hxs, hus, hqs, hXs⟩ := h
  refine ⟨xs, fun n => qs n + a, Xs, fun n => subJet_of_sub_linear (hj n),
    hxs, ?_, hqs.add tendsto_const_nhds, hXs⟩
  have hlin : Tendsto (fun n => inner ℝ a (xs n)) atTop (𝓝 (inner ℝ a x)) :=
    ((continuous_const.inner continuous_id).tendsto x).comp hxs
  have := hus.add hlin
  simpa using this

end shift

/-- A coefficient bounded near zero by a quadratic vanishes: if
`t a ≤ t² C` for `t` near zero, then `a = 0`. -/
theorem eq_zero_of_eventually_mul_le {a C : ℝ}
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), t * a ≤ t ^ 2 * C) : a = 0 := by
  by_contra ha
  have ha2 : 0 < a ^ 2 := by positivity
  have hcomp : Tendsto (fun s : ℝ => a * s) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun s : ℝ => a * s) (𝓝 0) (𝓝 (a * 0)) :=
      (continuous_mul_left a).tendsto 0
    rw [mul_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), (a * s) * a ≤ (a * s) ^ 2 * C :=
    hcomp.eventually h
  have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s * (|C| + 1) < 1 / 2 := by
    have hc : Tendsto (fun s : ℝ => s * (|C| + 1)) (𝓝[>] 0) (𝓝 0) := by
      have h0 : Tendsto (fun s : ℝ => s * (|C| + 1)) (𝓝 0) (𝓝 (0 * (|C| + 1))) :=
        (continuous_mul_right (|C| + 1)).tendsto 0
      rw [zero_mul] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    exact hc.eventually (gt_mem_nhds (by norm_num))
  have h3 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
  obtain ⟨s, hs1, hs2, hs3⟩ := (h1.and (h2.and h3)).exists
  -- s a² ≤ s² a² C, so a² ≤ s a² C ≤ s a² |C| < a²/2
  have e1 : s * a ^ 2 ≤ s ^ 2 * a ^ 2 * C := by nlinarith
  have e2 : a ^ 2 ≤ s * a ^ 2 * C := by
    have := e1
    have hs : 0 < s := hs3
    nlinarith
  have e3 : s * a ^ 2 * C ≤ s * a ^ 2 * |C| := by
    have : 0 ≤ s * a ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left (le_abs_self C) this
  have e4 : s * a ^ 2 * |C| ≤ s * (|C| + 1) * a ^ 2 := by
    have : 0 ≤ s * a ^ 2 := by positivity
    nlinarith
  nlinarith

/-- A quadratic coefficient bounded by every positive multiple vanishes from
above: if `t² b ≤ t² η` for `t` near zero, for every `η > 0`, then `b ≤ 0`. -/
theorem nonpos_of_eventually_sq {b : ℝ}
    (h : ∀ η > 0, ∀ᶠ t in 𝓝 (0 : ℝ), t ^ 2 * b ≤ t ^ 2 * η) : b ≤ 0 := by
  refine le_of_forall_pos_le_add (fun η hη => ?_)
  have h1 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ^ 2 * b ≤ t ^ 2 * η :=
    Eventually.filter_mono nhdsWithin_le_nhds (h η hη)
  have h3 : ∀ᶠ t in 𝓝[≠] (0 : ℝ), t ≠ 0 := self_mem_nhdsWithin
  obtain ⟨t, ht2, ht1⟩ := (h1.and h3).exists
  have hpos : 0 < t ^ 2 := by positivity
  have := le_of_mul_le_mul_left ht2 hpos
  linarith

/-- **The second-order condition at a maximum.** -/
theorem localMax_subJet {f : EuclSpace d → ℝ} {x q : EuclSpace d}
    {X : Bilin d} (hmax : IsLocalMax f x) (hj : (q, X) ∈ SubJet f x) :
    q = 0 ∧ QuadLE X 0 := by
  -- along every line through x
  have hline : ∀ v : EuclSpace d, ∀ η > 0, ∀ᶠ t in 𝓝 (0 : ℝ),
      t * inner ℝ q v + t ^ 2 * ((1 / 2) * (X v) v) ≤ t ^ 2 * (η * ‖v‖ ^ 2) := by
    intro v η hη
    have hT : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
      have h0 : Continuous (fun t : ℝ => x + t • v) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have := h0.tendsto 0
      simpa using this
    have h1 := hT.eventually (hj η hη)
    have h2 := hT.eventually hmax
    filter_upwards [h1, h2] with t ht1 ht2
    change f x + inner ℝ q (x + t • v - x) + (1 / 2) * (X (x + t • v - x))
      (x + t • v - x) - η * ‖x + t • v - x‖ ^ 2 ≤ f (x + t • v) at ht1
    change f (x + t • v) ≤ f x at ht2
    have hsub : x + t • v - x = t • v := by abel
    rw [hsub] at ht1
    simp only [inner_smul_right, map_smul, smul_eq_mul, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, ContinuousLinearMap.smul_apply] at ht1
    nlinarith
  -- the gradient vanishes
  have hq : q = 0 := by
    have hzero : inner ℝ q q = 0 := by
      apply eq_zero_of_eventually_mul_le (C := ‖q‖ ^ 2 - (1 / 2) * (X q) q)
      filter_upwards [hline q 1 one_pos] with t ht
      nlinarith
    exact inner_self_eq_zero.1 hzero
  refine ⟨hq, fun v => ?_⟩
  -- the form is nonpositive
  have hb : (1 / 2) * (X v) v - ‖v‖ ^ 2 * 0 ≤ 0 := by
    have : (1 / 2) * (X v) v ≤ 0 := by
      apply nonpos_of_eventually_sq (b := (1 / 2) * (X v) v)
      intro η hη
      have hη' : 0 < η / (‖v‖ ^ 2 + 1) := by positivity
      filter_upwards [hline v (η / (‖v‖ ^ 2 + 1)) hη'] with t ht
      rw [hq, inner_zero_left, mul_zero, zero_add] at ht
      have hle : η / (‖v‖ ^ 2 + 1) * ‖v‖ ^ 2 ≤ η := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [sq_nonneg ‖v‖]
      have ht2 : 0 ≤ t ^ 2 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hle ht2]
    linarith
  simp only [ContinuousLinearMap.zero_apply]
  linarith

/-- **The semiconvex Hessian bound.** -/
theorem semiconvex_superJet {lam : ℝ} {w : EuclSpace d → ℝ}
    (hw : SemiconvexWith lam w) {x q : EuclSpace d} {X : Bilin d}
    (hj : (q, X) ∈ SuperJet w x) (v : EuclSpace d) :
    -lam * ‖v‖ ^ 2 ≤ (X v) v := by
  -- convexity at the midpoint of x ± t v
  have hmid : ∀ t : ℝ, 2 * w x ≤ w (x + t • v) + w (x - t • v)
      + lam * t ^ 2 * ‖v‖ ^ 2 := by
    intro t
    have hc := hw.2 (mem_univ (x + t • v)) (mem_univ (x - t • v))
      (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2)
      (by norm_num : (1:ℝ) / 2 + 1 / 2 = 1)
    have hm : (1 / 2 : ℝ) • (x + t • v) + (1 / 2 : ℝ) • (x - t • v) = x := by
      module
    rw [hm] at hc
    simp only [smul_eq_mul] at hc
    have hp1 := norm_add_sq_real x (t • v)
    have hp2 := norm_sub_sq_real x (t • v)
    have hn : ‖t • v‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hkey : lam / 2 * ‖x + t • v‖ ^ 2 + lam / 2 * ‖x - t • v‖ ^ 2
        = lam * ‖x‖ ^ 2 + lam * t ^ 2 * ‖v‖ ^ 2 := by
      rw [hp1, hp2, hn]; ring
    linarith [hc, hkey]
  have hT : ∀ s : ℝ, Tendsto (fun t : ℝ => x + (s * t) • v) (𝓝 0) (𝓝 x) := by
    intro s
    have h0 : Continuous (fun t : ℝ => x + (s * t) • v) :=
      continuous_const.add ((continuous_const.mul continuous_id).smul continuous_const)
    have := h0.tendsto 0
    simpa using this
  have key : ∀ η > 0, ∀ᶠ t in 𝓝 (0 : ℝ),
      t ^ 2 * (-(X v) v - lam * ‖v‖ ^ 2) ≤ t ^ 2 * (2 * η * ‖v‖ ^ 2) := by
    intro η hη
    have hp := (hT 1).eventually (hj η hη)
    have hm := (hT (-1)).eventually (hj η hη)
    filter_upwards [hp, hm] with t h1 h2
    change w (x + (1 * t) • v) ≤ w x + inner ℝ q (x + (1 * t) • v - x)
      + (1 / 2) * (X (x + (1 * t) • v - x)) (x + (1 * t) • v - x)
      + η * ‖x + (1 * t) • v - x‖ ^ 2 at h1
    change w (x + (-1 * t) • v) ≤ w x + inner ℝ q (x + (-1 * t) • v - x)
      + (1 / 2) * (X (x + (-1 * t) • v - x)) (x + (-1 * t) • v - x)
      + η * ‖x + (-1 * t) • v - x‖ ^ 2 at h2
    have e1 : x + (1 * t) • v - x = t • v := by simp
    have e2 : x + (-1 * t) • v - x = -(t • v) := by
      rw [neg_one_mul, neg_smul]; abel
    have e3 : x + (-1 * t) • v = x - t • v := by
      rw [neg_one_mul, neg_smul, ← sub_eq_add_neg]
    have e4 : x + (1 * t) • v = x + t • v := by rw [one_mul]
    rw [e1, e4] at h1
    rw [e2, e3] at h2
    simp only [inner_smul_right, inner_neg_right, map_smul, map_neg, smul_eq_mul,
      norm_smul, norm_neg, Real.norm_eq_abs, mul_pow, sq_abs,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply] at h1 h2
    have hm' := hmid t
    nlinarith
  have hb : -(X v) v - lam * ‖v‖ ^ 2 ≤ 0 := by
    apply nonpos_of_eventually_sq
    intro η hη
    have hη' : 0 < η / (2 * (‖v‖ ^ 2 + 1)) := by positivity
    filter_upwards [key _ hη'] with t ht
    have hle : 2 * (η / (2 * (‖v‖ ^ 2 + 1))) * ‖v‖ ^ 2 ≤ η := by
      rw [show 2 * (η / (2 * (‖v‖ ^ 2 + 1))) * ‖v‖ ^ 2
          = η * (‖v‖ ^ 2 / (‖v‖ ^ 2 + 1)) by field_simp]
      have : ‖v‖ ^ 2 / (‖v‖ ^ 2 + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      nlinarith
    have ht2 : 0 ≤ t ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hle ht2]
  linarith

end

end PLaplacian
