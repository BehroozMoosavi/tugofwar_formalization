/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.SupConvJet

/-! # The gradient estimate at a maximum

Let `x` be a local maximum of `U - W` on `B(x, ρ)`, with `U` semiconvex
(constant `λ`), `-W` semiconvex (constant `μ`), and `q` a lower support of `U`
at `x`:

  `U(x) + ⟪q, y - x⟫ - (λ/2)|y - x|² ≤ U(y)` for all `y`.

1. `q` is also an upper support near `x`: the upper support of `W` at `x`
   must equal `q`, since their difference `v` satisfies
   `⟪v, y - x⟫ ≤ ((λ + μ)/2)|y - x|²` in every direction.
2. A lower support `a` of `U` at `y`, `|y - x| < ρ/3`, satisfies
   `|a - q| ≤ (λ + 2μ)|y - x|`: testing in the direction of `a - q` at scale
   `t ≥ |y - x|` gives `t |a - q| ≤ (λ + 2μ) t²`.

A subjet of a semiconvex function is a global lower support, by convexity along
segments; so at Alexandrov points the gradient is a lower support, and the
estimate applies to it.
-/

open Set Topology Filter Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- The square of `‖y‖` about `x`. -/
theorem norm_sq_about' (x y : EuclSpace d) :
    ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ 2 := by
  have e : y = x + (y - x) := by abel
  conv_lhs => rw [e]
  rw [norm_add_sq_real]

/-! ## Lower supports -/

/-- **A semiconvex function has a lower support at every point.** -/
theorem semiconvex_support {lam : ℝ} {f : EuclSpace d → ℝ} (h : SemiconvexWith lam f)
    (x : EuclSpace d) :
    ∃ q, ∀ y, f x + inner ℝ q (y - x) - lam / 2 * ‖y - x‖ ^ 2 ≤ f y := by
  obtain ⟨P, hP⟩ := subgrad_exists h x
  refine ⟨P - lam • x, fun y => ?_⟩
  have h1 : f x + lam / 2 * ‖x‖ ^ 2 + inner ℝ P (y - x) ≤ f y + lam / 2 * ‖y‖ ^ 2 := hP y
  have hn := congrArg (fun t => lam / 2 * t) (norm_sq_about' x y)
  rw [inner_sub_left, real_inner_smul_left]
  linarith

/-- **A subjet of a convex function is a subgradient.** -/
theorem convex_subJet_isSubgrad {f : EuclSpace d → ℝ} (hf : ConvexOn ℝ univ f)
    {y g : EuclSpace d} {X : Bilin d} (hj : (g, X) ∈ SubJet f y) : IsSubgrad f y g := by
  intro z
  by_contra hcon
  push Not at hcon
  set v := z - y with hv
  set D := f y + inner ℝ g v - f z with hD
  have hD0 : 0 < D := by linarith
  set C := 1 / 2 * ‖X‖ * ‖v‖ ^ 2 + ‖v‖ ^ 2 with hC
  have hC0 : 0 ≤ C := by positivity
  have hj' : ∀ η > 0, ∀ᶠ w in 𝓝 y, f y + inner ℝ g (w - y)
      + 1 / 2 * (X (w - y)) (w - y) - η * ‖w - y‖ ^ 2 ≤ f w := hj
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hj' 1 one_pos)
  set t := min (1 / 2) (min (ε / (2 * (‖v‖ + 1))) (D / (2 * (C + 1)))) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have ht2 : t ≤ ε / (2 * (‖v‖ + 1)) := le_trans (min_le_right _ _) (min_le_left _ _)
  have ht3 : t ≤ D / (2 * (C + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
  -- the point y + t v
  have hdist : dist (y + t • v) y < ε := by
    rw [dist_eq_norm]
    have e : y + t • v - y = t • v := by abel
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    have h1 : t * (2 * (‖v‖ + 1)) ≤ ε := (le_div_iff₀ (by positivity)).1 ht2
    nlinarith [norm_nonneg v]
  have h1 := hball hdist
  have e : y + t • v - y = t • v := by abel
  have hXt : (X (t • v)) (t • v) = t * (t * (X v) v) := by
    simp only [map_smul, smul_apply, smul_eq_mul]
  rw [e, real_inner_smul_right, hXt, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at h1
  -- convexity along the segment
  have hconv := hf.2 (mem_univ y) (mem_univ z) (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le
    (by ring : (1 - t) + t = 1)
  have e2 : (1 - t) • y + t • z = y + t • v := by rw [hv]; module
  rw [e2, smul_eq_mul, smul_eq_mul] at hconv
  -- the bound on the quadratic term
  have hXb : |(X v) v| ≤ ‖X‖ * ‖v‖ ^ 2 := by
    have := X.le_opNorm₂ v v
    rw [Real.norm_eq_abs] at this
    nlinarith
  have hq : t * D ≤ t ^ 2 * C := by
    have k := (abs_le.1 hXb).1
    nlinarith
  have hDC : D ≤ t * C := by nlinarith
  have hfin : t * C < D := by
    have h3 : t * (2 * (C + 1)) ≤ D := (le_div_iff₀ (by positivity)).1 ht3
    nlinarith
  linarith

/-- **A subjet of a semiconvex function is a global lower support.** -/
theorem semiconvex_subJet_support {lam : ℝ} {f : EuclSpace d → ℝ} (h : SemiconvexWith lam f)
    {y a : EuclSpace d} {A : Bilin d} (hj : (a, A) ∈ SubJet f y) :
    ∀ z, f y + inner ℝ a (z - y) - lam / 2 * ‖z - y‖ ^ 2 ≤ f z := by
  have hj' : ∀ η > 0, ∀ᶠ w in 𝓝 y, f y + inner ℝ a (w - y)
      + 1 / 2 * (A (w - y)) (w - y) - η * ‖w - y‖ ^ 2 ≤ f w := hj
  have hΦ : (a + lam • y, A + lam • idForm d)
      ∈ SubJet (fun z => f z + lam / 2 * ‖z‖ ^ 2) y := by
    intro η hη
    filter_upwards [hj' η hη] with w hw
    change f y + lam / 2 * ‖y‖ ^ 2 + inner ℝ (a + lam • y) (w - y)
      + 1 / 2 * ((A + lam • idForm d) (w - y)) (w - y) - η * ‖w - y‖ ^ 2
      ≤ f w + lam / 2 * ‖w‖ ^ 2
    rw [inner_add_left, real_inner_smul_left, add_apply, add_apply, smul_apply, smul_apply,
      smul_eq_mul, idForm_apply]
    have hn := congrArg (fun t => lam / 2 * t) (norm_sq_about' y w)
    linarith
  have hsg := convex_subJet_isSubgrad h hΦ
  intro z
  have h1 : f y + lam / 2 * ‖y‖ ^ 2 + inner ℝ (a + lam • y) (z - y)
      ≤ f z + lam / 2 * ‖z‖ ^ 2 := hsg z
  rw [inner_add_left, real_inner_smul_left] at h1
  have hn := congrArg (fun t => lam / 2 * t) (norm_sq_about' y z)
  linarith

/-! ## The estimate at a maximum -/

section max

variable {U W : EuclSpace d → ℝ} {x q : EuclSpace d} {ρ lam μ : ℝ}

/-- **The lower support at a maximum is also an upper support.** -/
theorem upper_support_of_max (hlam : 0 ≤ lam) (hμ : 0 ≤ μ) (hρ : 0 < ρ)
    (hW : SemiconvexWith μ (fun y => -W y))
    (hmax : ∀ y ∈ ball x ρ, U y - W y ≤ U x - W x)
    (hq : ∀ y, U x + inner ℝ q (y - x) - lam / 2 * ‖y - x‖ ^ 2 ≤ U y) :
    ∀ y ∈ ball x ρ, U y ≤ U x + inner ℝ q (y - x) + μ / 2 * ‖y - x‖ ^ 2 := by
  obtain ⟨P, hP⟩ := semiconvex_support hW x
  -- the upper support of W at x
  have hWu : ∀ y, W y ≤ W x - inner ℝ P (y - x) + μ / 2 * ‖y - x‖ ^ 2 := fun y => by
    have := hP y
    linarith
  -- it equals q
  have hPq : q + P = 0 := by
    by_contra hv
    set v := q + P with hvdef
    have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
    set t := min (ρ / (2 * (‖v‖ + 1))) (1 / (lam + μ + 1)) with ht
    have ht0 : 0 < t := lt_min (by positivity) (by positivity)
    have ht1 : t ≤ ρ / (2 * (‖v‖ + 1)) := min_le_left _ _
    have ht2 : t ≤ 1 / (lam + μ + 1) := min_le_right _ _
    have hy : x + t • v ∈ ball x ρ := by
      rw [mem_ball, dist_eq_norm]
      have e : x + t • v - x = t • v := by abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have h1 : t * (2 * (‖v‖ + 1)) ≤ ρ := (le_div_iff₀ (by positivity)).1 ht1
      nlinarith [norm_nonneg v]
    have h1 := hq (x + t • v)
    have h2 := hmax (x + t • v) hy
    have h3 := hWu (x + t • v)
    have e : x + t • v - x = t • v := by abel
    rw [e, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at h1 h3
    -- ⟪v, t v⟫ ≤ ((λ + μ)/2) t² ‖v‖²
    have key : t * inner ℝ v v ≤ (lam + μ) / 2 * (t * ‖v‖) ^ 2 := by
      rw [hvdef, inner_add_left]
      linarith
    rw [real_inner_self_eq_norm_sq] at key
    have h4 : t * (lam + μ + 1) ≤ 1 := (le_div_iff₀ (by positivity)).1 ht2
    have h5 : (lam + μ) / 2 * (t * ‖v‖) ^ 2 < t * ‖v‖ ^ 2 := by
      have : (lam + μ) * t < 2 := by nlinarith
      have hpos : 0 < t * ‖v‖ ^ 2 := by positivity
      nlinarith
    linarith
  have hPeq : P = -q := by
    have := hPq
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact this
  intro y hy
  have h1 := hmax y hy
  have h2 := hWu y
  rw [hPeq, inner_neg_left] at h2
  linarith

/-- **The gradient estimate**: lower supports at nearby points are close to `q`. -/
theorem grad_est (hlam : 0 ≤ lam) (hμ : 0 ≤ μ) (hρ : 0 < ρ)
    (hW : SemiconvexWith μ (fun y => -W y))
    (hmax : ∀ y ∈ ball x ρ, U y - W y ≤ U x - W x)
    (hq : ∀ y, U x + inner ℝ q (y - x) - lam / 2 * ‖y - x‖ ^ 2 ≤ U y)
    {y a : EuclSpace d} (hy : ‖y - x‖ < ρ / 3)
    (ha : ∀ z, U y + inner ℝ a (z - y) - lam / 2 * ‖z - y‖ ^ 2 ≤ U z) :
    ‖a - q‖ ≤ (lam + 2 * μ) * ‖y - x‖ := by
  have hup := upper_support_of_max hlam hμ hρ hW hmax hq
  set s := ‖y - x‖ with hs
  have hs0 : 0 ≤ s := norm_nonneg _
  -- the estimate at every scale t ≥ s
  have hscale : ∀ t, s ≤ t → t < ρ / 3 → ‖a - q‖ ≤ (lam + 2 * μ) * t := by
    intro t hst htρ
    have ht0 : 0 ≤ t := le_trans hs0 hst
    rcases eq_or_ne (a - q) 0 with h0 | h0
    · rw [h0, norm_zero]; positivity
    have hn : 0 < ‖a - q‖ := norm_pos_iff.2 h0
    rcases eq_or_lt_of_le ht0 with ht | ht
    · -- t = 0 forces s = 0
      have hs' : s = 0 := le_antisymm (by rw [← ht] at hst; exact hst) hs0
      -- then y = x, and a, q are both lower supports at x
      have hyx : y = x := by
        have : ‖y - x‖ = 0 := hs'
        exact sub_eq_zero.1 (norm_eq_zero.1 this)
      -- a ≠ q is impossible: the estimate at arbitrarily small scales
      exfalso
      have hsmall : ∀ τ, 0 < τ → τ < ρ / 3 → ‖a - q‖ ≤ (lam + μ) / 2 * τ := by
        intro τ hτ0 hτρ
        set e := ‖a - q‖⁻¹ • (a - q) with he
        have he1 : ‖e‖ = 1 := by
          rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
        have hz : x + τ • e ∈ ball x ρ := by
          rw [mem_ball, dist_eq_norm]
          have e0 : x + τ • e - x = τ • e := by abel
          rw [e0, norm_smul, he1, Real.norm_eq_abs, abs_of_pos hτ0, mul_one]
          linarith
        have h1 := ha (x + τ • e)
        have h2 := hup _ hz
        rw [hyx] at h1
        have e0 : x + τ • e - x = τ • e := by abel
        rw [e0, real_inner_smul_right, norm_smul, he1, Real.norm_eq_abs, abs_of_pos hτ0,
          mul_one] at h1 h2
        have hae : inner ℝ (a - q) e = ‖a - q‖ := by
          rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq]
          field_simp
        have k : τ * inner ℝ (a - q) e ≤ (lam + μ) / 2 * τ ^ 2 := by
          rw [inner_sub_left]
          linarith
        rw [hae] at k
        by_contra hc
        push Not at hc
        have := mul_lt_mul_of_pos_left hc hτ0
        nlinarith
      set τ := min (ρ / 6) (‖a - q‖ / ((lam + μ) / 2 + 1)) with hτ
      have hτ0 : 0 < τ := lt_min (by positivity) (by positivity)
      have hτ1 : τ ≤ ρ / 6 := min_le_left _ _
      have hτ2 : τ ≤ ‖a - q‖ / ((lam + μ) / 2 + 1) := min_le_right _ _
      have h1 := hsmall τ hτ0 (by linarith)
      have h2 : τ * ((lam + μ) / 2 + 1) ≤ ‖a - q‖ := (le_div_iff₀ (by positivity)).1 hτ2
      nlinarith
    · -- t > 0: test in the direction of a - q at scale t
      set e := ‖a - q‖⁻¹ • (a - q) with he
      have he1 : ‖e‖ = 1 := by
        rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
      set z := y + t • e with hzdef
      have hzx : ‖z - x‖ ≤ s + t := by
        have e0 : z - x = (y - x) + t • e := by rw [hzdef]; abel
        rw [e0]
        calc ‖(y - x) + t • e‖ ≤ ‖y - x‖ + ‖t • e‖ := norm_add_le _ _
          _ = s + t := by rw [norm_smul, he1, Real.norm_eq_abs, abs_of_pos ht, mul_one]
      have hz : z ∈ ball x ρ := by
        rw [mem_ball, dist_eq_norm]; linarith
      have h1 := ha z
      have h2 := hup z hz
      have h3 := hq y
      have e1 : z - y = t • e := by rw [hzdef]; abel
      have e2 : z - x = (y - x) + t • e := by rw [hzdef]; abel
      rw [e1, real_inner_smul_right, norm_smul, he1, Real.norm_eq_abs, abs_of_pos ht,
        mul_one] at h1
      rw [e2, inner_add_right, real_inner_smul_right] at h2
      rw [← e2] at h2
      have hzx2 : ‖z - x‖ ^ 2 ≤ (s + t) ^ 2 := by
        have := mul_self_le_mul_self (norm_nonneg _) hzx
        nlinarith
      have hae : inner ℝ (a - q) e = ‖a - q‖ := by
        rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      have k : t * inner ℝ (a - q) e
          ≤ lam / 2 * t ^ 2 + μ / 2 * ‖z - x‖ ^ 2 + lam / 2 * s ^ 2 := by
        rw [inner_sub_left]
        linarith
      rw [hae] at k
      have k2 : lam / 2 * t ^ 2 + μ / 2 * ‖z - x‖ ^ 2 + lam / 2 * s ^ 2
          ≤ (lam + 2 * μ) * t ^ 2 := by
        have a1 : μ / 2 * ‖z - x‖ ^ 2 ≤ μ / 2 * (s + t) ^ 2 :=
          mul_le_mul_of_nonneg_left hzx2 (by positivity)
        have a2 : (s + t) ^ 2 ≤ 4 * t ^ 2 := by nlinarith
        have a3 : s ^ 2 ≤ t ^ 2 := by nlinarith
        nlinarith
      have : t * ‖a - q‖ ≤ t * ((lam + 2 * μ) * t) := by nlinarith
      exact le_of_mul_le_mul_left this ht
  -- let the scale decrease to s
  by_contra hcon
  push Not at hcon
  set gap := ‖a - q‖ - (lam + 2 * μ) * s with hgap
  have hgap0 : 0 < gap := by linarith
  set τ := min ((ρ / 3 - s) / 2) (gap / (2 * (lam + 2 * μ + 1))) with hτ
  have hτ0 : 0 < τ := lt_min (by linarith) (by positivity)
  have hτ1 : τ ≤ (ρ / 3 - s) / 2 := min_le_left _ _
  have hτ2 : τ ≤ gap / (2 * (lam + 2 * μ + 1)) := min_le_right _ _
  have h1 := hscale (s + τ) (by linarith) (by linarith)
  have h2 : τ * (2 * (lam + 2 * μ + 1)) ≤ gap := (le_div_iff₀ (by positivity)).1 hτ2
  nlinarith

end max

end

end PLaplacian
