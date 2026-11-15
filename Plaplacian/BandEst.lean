/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.RegPair

@[expose] public section

/-! # The band estimate

If `U ≤ V` on `∂Ω`, then for every `θ > 0` there are `δ > 0` and `Λ` with
`U_λ - V_λ ≤ θ` on `{x ∈ Ω̄ : dist(x, Ωᶜ) ≤ 2δ}` for all `λ ≥ Λ`.

Otherwise, for each `n` there are `λₙ ≥ n + 1` and `xₙ` within `2/(n + 1)` of
`Ωᶜ` with `U_λₙ(xₙ) - V_λₙ(xₙ) > θ`.

1. With maximizers `yₙ`, `zₙ`: `U_λₙ(xₙ) ≤ U(yₙ)`, `V_λₙ(xₙ) ≥ V(zₙ)`, and
   `|yₙ - xₙ|², |zₙ - xₙ|² ≤ 2·osc/(n + 1)`; so `θ < U(yₙ) - V(zₙ)`.
2. A subsequence `x_φ(n) → x*`, with `dist(x*, Ωᶜ) = 0`, so `x* ∈ ∂Ω`; and
   `y_φ(n), z_φ(n) → x*`.
3. Eventually `U(y) < U(x*) + θ/2` and `V(z) > V(x*) - θ/2`, so
   `θ < U(x*) - V(x*) + θ ≤ θ`.
-/

open Set Topology Filter Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- **A bounded set in `ℝᵈ`, `d ≥ 1`, has nonempty complement.** -/
theorem compl_nonempty (hd : 0 < d) {Ω : Set (EuclSpace d)} (hb : Bornology.IsBounded Ω) :
    (Ωᶜ).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty, compl_empty_iff] at h
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
  set e := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) with he
  have hen : ‖e‖ = 1 := by rw [he]; simp
  have h1 := hC ((|C| + 1) • e) (by rw [h]; exact mem_univ _)
  rw [norm_smul, hen, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
  have := le_abs_self C
  linarith

/-- Norms tend to zero when their squares do. -/
theorem tendsto_norm_of_sq {v : ℕ → EuclSpace d}
    (h : Tendsto (fun n => ‖v n‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ‖v n‖) atTop (𝓝 0) := by
  have h1 := (Real.continuous_sqrt.tendsto 0).comp h
  rw [Real.sqrt_zero] at h1
  refine h1.congr fun n => ?_
  simp [Function.comp, Real.sqrt_sq (norm_nonneg _)]

set_option maxHeartbeats 800000 in
-- Sequences, a subsequence, and semicontinuity at the limit.
/-- **The band estimate.** -/
theorem band_est {Ω : Set (EuclSpace d)} (hΩb : Bornology.IsBounded Ω) (hΩc : (Ωᶜ).Nonempty)
    {U V : EuclSpace d → ℝ} (hU : UpperSemicontinuous U) (hV : LowerSemicontinuous V)
    (hUb : BddAbove (range U)) (hVb : BddBelow (range V))
    {SU SL TU TL : ℝ} (hSU : ∀ x, U x ≤ SU) (hSL : ∀ x, SL ≤ U x)
    (hTU : ∀ x, V x ≤ TU) (hTL : ∀ x, TL ≤ V x)
    (hbd : ∀ x ∈ frontier Ω, U x ≤ V x) {θ : ℝ} (hθ : 0 < θ) :
    ∃ δ > 0, ∃ Λ > 0, ∀ lam, Λ ≤ lam → ∀ x ∈ closure Ω, infDist x Ωᶜ ≤ 2 * δ →
      regU lam U x - regV lam V x ≤ θ := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ (lam : ℝ) (x : EuclSpace d), (n : ℝ) + 1 ≤ lam ∧ x ∈ closure Ω ∧
      infDist x Ωᶜ ≤ 2 * (1 / ((n : ℝ) + 1)) ∧ θ < regU lam U x - regV lam V x := by
    intro n
    obtain ⟨lam, hl, x, hx, h1, h2⟩ := hcon (1 / ((n : ℝ) + 1)) (by positivity) ((n : ℝ) + 1)
      (by positivity)
    exact ⟨lam, x, hl, hx, h1, h2⟩
  choose lams xs hlam hxs hinf hgt using hseq
  have hlam0 : ∀ n, 0 < lams n := fun n => lt_of_lt_of_le (by positivity) (hlam n)
  -- the maximizers
  have hb := bddAbove_neg_of_bddBelow hVb
  choose ys hys using fun n => supConv_attained (hlam0 n) hU hUb (xs n)
  choose zs hzs using fun n => supConv_attained (hlam0 n) (usc_neg_of_lsc hV) hb (xs n)
  -- θ < U(y) - V(z)
  have hUV : ∀ n, θ < U (ys n) - V (zs n) := by
    intro n
    have h1 := hgt n
    have e1 : regU (lams n) U (xs n) = supConv (lams n) U (xs n) := rfl
    have e2 : regV (lams n) V (xs n) = -supConv (lams n) (fun y => -V y) (xs n) := rfl
    rw [e1, e2, hys n, hzs n] at h1
    have a1 : 0 ≤ lams n / 2 * ‖ys n - xs n‖ ^ 2 := by have := hlam0 n; positivity
    have a2 : 0 ≤ lams n / 2 * ‖zs n - xs n‖ ^ 2 := by have := hlam0 n; positivity
    linarith
  -- the maximizers are close
  have hCU : 0 ≤ SU - SL := by linarith [hSU 0, hSL 0]
  have hCV : 0 ≤ TU - TL := by linarith [hTU 0, hTL 0]
  have hyclose : ∀ n, ‖ys n - xs n‖ ^ 2 ≤ 2 * (SU - SL) / ((n : ℝ) + 1) := by
    intro n
    have h1 := supConv_maximizer_close (hlam0 n).le hUb hSU (hys n)
    have h2 := hSL (xs n)
    have h3 : ‖ys n - xs n‖ ^ 2 ≤ 2 * (SU - SL) / lams n := by
      rw [le_div_iff₀ (hlam0 n)]; nlinarith
    exact h3.trans (div_le_div_of_nonneg_left (by linarith) (by positivity) (hlam n))
  have hzclose : ∀ n, ‖zs n - xs n‖ ^ 2 ≤ 2 * (TU - TL) / ((n : ℝ) + 1) := by
    intro n
    have h1 := supConv_maximizer_close (hlam0 n).le hb
      (fun x => (by linarith [hTL x] : -V x ≤ -TL)) (hzs n)
    have h2 := hTU (xs n)
    have h3 : ‖zs n - xs n‖ ^ 2 ≤ 2 * (TU - TL) / lams n := by
      rw [le_div_iff₀ (hlam0 n)]; nlinarith
    exact h3.trans (div_le_div_of_nonneg_left (by linarith) (by positivity) (hlam n))
  -- a convergent subsequence
  obtain ⟨xstar, hxstar, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hΩb.closure hxs
  have hφT : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  -- x* lies on the frontier
  have hinf0 : infDist xstar Ωᶜ = 0 := by
    have h1 : Tendsto (fun n => infDist (xs (φ n)) Ωᶜ) atTop (𝓝 (infDist xstar Ωᶜ)) :=
      ((continuous_infDist_pt Ωᶜ).tendsto xstar).comp hlim
    have h2 : Tendsto (fun n => 2 * (1 / ((φ n : ℝ) + 1))) atTop (𝓝 (2 * 0)) :=
      hφT.const_mul 2
    rw [mul_zero] at h2
    have h3 := le_of_tendsto_of_tendsto' h1 h2 (fun n => hinf (φ n))
    exact le_antisymm h3 infDist_nonneg
  have hfr : xstar ∈ frontier Ω := by
    rw [frontier_eq_closure_inter_closure]
    refine ⟨by rwa [closure_closure] at hxstar, ?_⟩
    exact (mem_closure_iff_infDist_zero hΩc).2 hinf0
  have hUVstar := hbd xstar hfr
  -- the maximizers converge to x*
  have hsqT : ∀ (w : ℕ → EuclSpace d) (C : ℝ), 0 ≤ C →
      (∀ n, ‖w n - xs n‖ ^ 2 ≤ 2 * C / ((n : ℝ) + 1)) →
      Tendsto (fun n => w (φ n)) atTop (𝓝 xstar) := by
    intro w C hC hw
    have h1 : Tendsto (fun n => ‖w (φ n) - xs (φ n)‖ ^ 2) atTop (𝓝 0) := by
      have h2 : Tendsto (fun n => 2 * C * (1 / ((φ n : ℝ) + 1))) atTop (𝓝 (2 * C * 0)) :=
        hφT.const_mul (2 * C)
      rw [mul_zero] at h2
      refine squeeze_zero (fun n => by positivity) (fun n => ?_) h2
      have := hw (φ n)
      rw [mul_one_div]
      exact this
    have h3 := tendsto_norm_of_sq (v := fun n => w (φ n) - xs (φ n)) h1
    have h4 : Tendsto (fun n => ‖xs (φ n) - xstar‖) atTop (𝓝 0) :=
      (tendsto_iff_norm_sub_tendsto_zero.1 hlim)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h5 : Tendsto (fun n => ‖w (φ n) - xs (φ n)‖ + ‖xs (φ n) - xstar‖) atTop (𝓝 0) := by
      have := h3.add h4
      rwa [add_zero] at this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h5
    have e : w (φ n) - xstar = (w (φ n) - xs (φ n)) + (xs (φ n) - xstar) := by abel
    rw [e]
    exact norm_add_le _ _
  have hyT := hsqT ys (SU - SL) hCU hyclose
  have hzT := hsqT zs (TU - TL) hCV hzclose
  -- semicontinuity at x*
  have hUev : ∀ᶠ n in atTop, U (ys (φ n)) < U xstar + θ / 2 :=
    hyT.eventually (hU xstar (U xstar + θ / 2) (by linarith))
  have hVev : ∀ᶠ n in atTop, V xstar - θ / 2 < V (zs (φ n)) :=
    hzT.eventually (hV xstar (V xstar - θ / 2) (by linarith))
  obtain ⟨n, h1, h2⟩ := (hUev.and hVev).exists
  have h3 := hUV (φ n)
  linarith

end

end PLaplacian
