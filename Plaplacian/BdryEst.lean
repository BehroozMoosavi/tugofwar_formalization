/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.BdryPrep

/-! # The boundary estimate

At `y₀ ∉ Ω` with an exterior ball `B(z₀, δ₀)` and `F` continuous at `y₀`,
`ubar u y₀ ≤ F y₀`.

1. (`bdry_compare`) For fixed `ε`, with the geometry stated as hypotheses: on
   `D = Ω ∩ {|x - z|² < δ² + τ}`, `u_ε ≤ c + A ψ`. The barrier is clamped, the
   strict supersolution property is transferred by locality, and the discrete
   comparison applies.
2. (`bdry_step`) With `z` the midpoint of `y₀` and `z₀`, `δ = δ₀/2`, `τ` small,
   `c = F(y₀) + 2η₁` and `A` large, Apollonius places `D` within `r₀/2` of `y₀`
   and checks every hypothesis; near `y₀`, `ψ ≤ t ≤ (2δ + 1) r₁`, so
   `u_ε ≤ F(y₀) + 3η₁`.
3. (`ubar_le_bdry`) The eventual bound gives `ubar u y₀ ≤ F(y₀) + η` for every `η`.
-/

open Set Topology Filter Metric MeasureTheory

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-! ## The comparison with the barrier -/

set_option maxHeartbeats 800000 in
-- The clamp, locality, and the discrete comparison.
theorem bdry_compare [Nontrivial (EuclSpace d)] (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε))
    (hout : ∀ ε > 0, ∀ x, x ∉ Ω → u ε x = F x)
    {δ : ℝ} (hδ : 0 < δ) (z : EuclSpace d) {c A τ a ε ε₀ : ℝ}
    (hA : 0 < A) (hτ0 : 0 ≤ τ) (ha : 0 ≤ a) (hε : 0 < ε)
    (hε₀ : ∀ y ∈ bShell z δ (bM p δ d), ∀ ε' : ℝ, 0 < ε' → ε' ≤ ε₀ →
      tugOfWarOp p ε' (fun x => c + A * bpsi z δ (bM p δ d) x) y
        ≤ (c + A * bpsi z δ (bM p δ d) y) - A * ε' ^ 2 / (4 * (p + (d : ℝ))))
    (hεε₀ : ε ≤ ε₀) (hMa : bM p δ d * a ≤ 1) (hτM : τ ≤ 1 / (4 * bM p δ d))
    (hG1 : ∀ x, x ∈ Ω → ‖x - z‖ ^ 2 < δ ^ 2 + τ → δ ^ 2 ≤ ‖x - z‖ ^ 2)
    (hG2 : ∀ w y, y ∈ Ω → ‖y - z‖ ^ 2 < δ ^ 2 + τ → dist w y < ε →
      -a ≤ ‖w - z‖ ^ 2 - δ ^ 2)
    (hG3 : ∀ w y, y ∈ Ω → ‖y - z‖ ^ 2 < δ ^ 2 + τ → dist w y < ε →
      ‖w - z‖ ^ 2 - δ ^ 2 ≤ 1 / (4 * bM p δ d))
    (hG4 : C ≤ c + A * (3 / 4 * τ))
    (hG5 : ∀ w y, w ∉ Ω → y ∈ Ω → ‖y - z‖ ^ 2 < δ ^ 2 + τ → dist w y < ε →
      F w ≤ c - 2 * A * a) :
    ∀ x, x ∈ Ω → ‖x - z‖ ^ 2 < δ ^ 2 + τ → u ε x ≤ c + A * bpsi z δ (bM p δ d) x := by
  set M := bM p δ d with hMdef
  have hp1 : 0 < p - 1 := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hM : 0 < M := by
    rw [hMdef]; unfold bM
    have hD : 0 < (d : ℝ) + p - 2 := by linarith
    exact div_pos (by linarith) (mul_pos (mul_pos (by norm_num) hp1) (pow_pos hδ 2))
  set D := {x | x ∈ Ω ∧ ‖x - z‖ ^ 2 < δ ^ 2 + τ} with hDdef
  set v : EuclSpace d → ℝ := fun x => c + A * bpsi z δ M x with hvdef
  have hvc : Continuous v :=
    continuous_const.add (continuous_const.mul (bpsi_contDiff z δ M (n := 0)).continuous)
  -- v is bounded on the ε-neighbourhood of D
  set Q := a + 1 / (4 * M) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set B := |c| + A * (Q + M * Q ^ 2) + 1 with hB
  have hB0 : 0 ≤ B := by positivity
  have hNb : ∀ w, (∃ y ∈ D, dist w y < ε) → |v w| ≤ B := by
    rintro w ⟨y, ⟨hyΩ, hyD⟩, hwy⟩
    have hlo := hG2 w y hyΩ hyD hwy
    have hhi := hG3 w y hyΩ hyD hwy
    have hq4 : 0 ≤ 1 / (4 * M) := by positivity
    have ht : |‖w - z‖ ^ 2 - δ ^ 2| ≤ Q := abs_le.2 ⟨by linarith, by linarith⟩
    have ht2 : (‖w - z‖ ^ 2 - δ ^ 2) ^ 2 ≤ Q ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) ht 2
    have hψ := abs_bpsi_le hM.le z δ w
    have hψQ : |bpsi z δ M w| ≤ Q + M * Q ^ 2 := by
      have := mul_le_mul_of_nonneg_left ht2 hM.le
      linarith
    change |c + A * bpsi z δ M w| ≤ B
    calc |c + A * bpsi z δ M w| ≤ |c| + |A * bpsi z δ M w| := abs_add_le _ _
      _ = |c| + A * |bpsi z δ M w| := by rw [abs_mul, abs_of_pos hA]
      _ ≤ |c| + A * (Q + M * Q ^ 2) := by
          have := mul_le_mul_of_nonneg_left hψQ hA.le
          linarith
      _ ≤ B := by rw [hB]; linarith
  set v' := clampF B v with hv'def
  have hv'eq : ∀ w, (∃ y ∈ D, dist w y < ε) → v' w = v w := fun w hw => clampF_eq (hNb w hw)
  have hself : ∀ x ∈ D, ∃ y ∈ D, dist x y < ε := fun x hx => ⟨x, hx, by rw [dist_self]; exact hε⟩
  -- the hypotheses of the discrete comparison
  have hU : ∀ x ∈ D, u ε x = tugOfWarOp p ε (u ε) x := fun x hx => (hu ε hε).interior x hx.1
  have hκ : 0 < A * ε ^ 2 / (4 * (p + (d : ℝ))) := by positivity
  have hV : ∀ x ∈ D, tugOfWarOp p ε v' x ≤ v' x - A * ε ^ 2 / (4 * (p + (d : ℝ))) := by
    intro x hx
    have hball : ∀ y ∈ ball x ε, v' y = v y := fun y hy =>
      hv'eq y ⟨x, hx, by rw [mem_ball] at hy; exact hy⟩
    rw [tugOfWarOp_congr_ball hball, hv'eq x (hself x hx)]
    have hsh : x ∈ bShell z δ M := ⟨hG1 x hx.1 hx.2, by linarith [hx.2]⟩
    exact hε₀ x hsh ε hε hεε₀
  have hstrip : ∀ w, w ∉ D → (∃ y ∈ D, dist w y < ε) → u ε w ≤ v' w := by
    intro w hwD hw
    rw [hv'eq w hw]
    obtain ⟨y, ⟨hyΩ, hyD⟩, hwy⟩ := hw
    have hhi := hG3 w y hyΩ hyD hwy
    by_cases hwΩ : w ∈ Ω
    · have ht : δ ^ 2 + τ ≤ ‖w - z‖ ^ 2 := by
        by_contra h
        push Not at h
        exact hwD ⟨hwΩ, h⟩
      have hψ := bpsi_nonneg hM z (by linarith : δ ^ 2 ≤ ‖w - z‖ ^ 2)
        (by linarith : ‖w - z‖ ^ 2 ≤ δ ^ 2 + 1 / (4 * M))
      have h1 : A * (3 / 4 * τ) ≤ A * bpsi z δ M w :=
        mul_le_mul_of_nonneg_left (by linarith) hA.le
      have h2 := (abs_le.1 (hC ε w)).2
      change u ε w ≤ c + A * bpsi z δ M w
      linarith
    · have h1 := hout ε hε w hwΩ
      have h2 := hG5 w y hwΩ hyΩ hyD hwy
      have hψ := bpsi_ge_neg hM z δ ha hMa (hG2 w y hyΩ hyD hwy) hhi
      have h3 : A * (-(2 * a)) ≤ A * bpsi z δ M w := mul_le_mul_of_nonneg_left hψ hA.le
      change u ε w ≤ c + A * bpsi z δ M w
      linarith
  have hcomp := disc_comparison hp hpd hε (hu ε hε).bddMeas (bddMeas_clampF hB0 hvc) hU hκ hV
    hstrip
  intro x hxΩ hxD
  have h1 := hcomp x ⟨hxΩ, hxD⟩
  change u ε x ≤ v' x at h1
  rw [hv'eq x (hself x ⟨hxΩ, hxD⟩)] at h1
  exact h1

/-! ## The parameters -/

set_option maxHeartbeats 1600000 in
-- The parameters, and the geometry checked through Apollonius.
theorem bdry_step [Nontrivial (EuclSpace d)] (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε))
    (hout : ∀ ε > 0, ∀ x, x ∉ Ω → u ε x = F x)
    {y₀ : EuclSpace d} (hFc : ContinuousAt F y₀)
    {z₀ : EuclSpace d} {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hy₀z : ‖y₀ - z₀‖ = δ₀)
    (hext : ∀ x ∈ Ω, δ₀ ≤ ‖x - z₀‖) {η₁ : ℝ} (hη₁ : 0 < η₁) :
    ∃ ε₁ > 0, ∃ r₁ > 0, ∀ ε, 0 < ε → ε < ε₁ → ∀ x ∈ ball y₀ r₁,
      u ε x ≤ F y₀ + 3 * η₁ := by
  obtain ⟨r₀, hr₀, hF⟩ := Metric.continuousAt_iff.1 hFc η₁ hη₁
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 0)
  -- the smaller exterior ball
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = δ₀ / 2 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  obtain ⟨z, hz⟩ : ∃ z, z = z₀ + (1 / 2 : ℝ) • (y₀ - z₀) := ⟨_, rfl⟩
  have hyz : ‖y₀ - z‖ = δ := by
    have e : y₀ - z = (1 / 2 : ℝ) • (y₀ - z₀) := by rw [hz]; module
    rw [e, norm_smul, hy₀z, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
      hδdef]
    ring
  -- the constants
  set M := bM p δ d with hMdef
  have hp1 : 0 < p - 1 := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hM : 0 < M := by
    rw [hMdef]; unfold bM
    have hD : 0 < (d : ℝ) + p - 2 := by linarith
    exact div_pos (by linarith) (mul_pos (mul_pos (by norm_num) hp1) (pow_pos hδ 2))
  set τ := min (1 / (8 * M)) (r₀ ^ 2 / 8) with hτdef
  have hτ : 0 < τ := lt_min (by positivity) (by positivity)
  have hτ1 : τ ≤ 1 / (8 * M) := min_le_left _ _
  have hτ2 : τ ≤ r₀ ^ 2 / 8 := min_le_right _ _
  have hτM : τ ≤ 1 / (4 * M) := by
    have : 1 / (8 * M) ≤ 1 / (4 * M) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith)
    linarith
  set c := F y₀ + 2 * η₁ with hc
  set A := 4 * (C + |c| + 1) / (3 * τ) with hAdef
  have hA : 0 < A := by positivity
  have hAτ : A * (3 / 4 * τ) = C + |c| + 1 := by rw [hAdef]; field_simp
  obtain ⟨ε₀, hε₀pos, hε₀⟩ := barrier_super hd hp hpd hδ z c hA
  set K3 := 2 * (δ ^ 2 + τ + 1) + 1 with hK3
  have hK30 : 0 < K3 := by positivity
  set ε₁ := min ε₀ (min (r₀ / 2) (min δ₀ (min 1 (min (η₁ / (2 * A * δ₀ + 1))
    (min (1 / (M * δ₀ + 1)) (1 / (8 * M * K3))))))) with hε₁def
  have hε₁ : 0 < ε₁ := by
    refine lt_min hε₀pos (lt_min (by positivity) (lt_min hδ₀ (lt_min one_pos
      (lt_min (by positivity) (lt_min (by positivity) (by positivity))))))
  set r₁ := min r₀ (min 1 (min (τ / (2 * δ + 2)) (η₁ / (A * (2 * δ + 1) + 1)))) with hr₁def
  have hr₁ : 0 < r₁ :=
    lt_min hr₀ (lt_min one_pos (lt_min (by positivity) (by positivity)))
  refine ⟨ε₁, hε₁, r₁, hr₁, fun ε hε hεε₁ x hx => ?_⟩
  -- the bounds on ε
  have hε1 : ε ≤ ε₀ := le_trans hεε₁.le (min_le_left _ _)
  have hε2 : ε ≤ r₀ / 2 := le_trans hεε₁.le (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε3 : ε ≤ δ₀ := le_trans hεε₁.le (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hε4 : ε ≤ 1 := le_trans hεε₁.le (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hε5 : ε ≤ η₁ / (2 * A * δ₀ + 1) := le_trans hεε₁.le (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have hε6 : ε ≤ 1 / (M * δ₀ + 1) := le_trans hεε₁.le (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))))
  have hε7 : ε ≤ 1 / (8 * M * K3) := le_trans hεε₁.le (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))))
  -- Apollonius, with e = 0 and with e = ε
  have hap : ∀ x, ∀ e : ℝ, 0 ≤ e → e ≤ δ₀ → δ₀ - e ≤ ‖x - z₀‖ →
      δ ^ 2 + ‖x - y₀‖ ^ 2 / 2 - δ₀ * e ≤ ‖x - z‖ ^ 2 := by
    intro x e he he' hx
    have h := apoll_ge hδ₀ hy₀z he he' hx
    rw [← hz, ← hδdef] at h
    exact h
  have hG1 : ∀ x, x ∈ Ω → ‖x - z‖ ^ 2 < δ ^ 2 + τ → δ ^ 2 ≤ ‖x - z‖ ^ 2 := by
    intro x hxΩ _
    have h := hap x 0 le_rfl hδ₀.le (by linarith [hext x hxΩ])
    have : 0 ≤ ‖x - y₀‖ ^ 2 / 2 := by positivity
    linarith
  have hclose : ∀ y, y ∈ Ω → ‖y - z‖ ^ 2 < δ ^ 2 + τ → ‖y - y₀‖ < r₀ / 2 := by
    intro y hyΩ hyD
    have h := hap y 0 le_rfl hδ₀.le (by linarith [hext y hyΩ])
    have h2 : ‖y - y₀‖ ^ 2 < (r₀ / 2) ^ 2 := by nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
  have hfar : ∀ w y, y ∈ Ω → dist w y < ε → δ₀ - ε ≤ ‖w - z₀‖ := by
    intro w y hyΩ hwy
    have h1 := hext y hyΩ
    have h2 : ‖y - z₀‖ ≤ ‖y - w‖ + ‖w - z₀‖ := by
      have := norm_add_le (y - w) (w - z₀)
      rwa [sub_add_sub_cancel] at this
    rw [dist_eq_norm, ← norm_neg, neg_sub] at hwy
    linarith
  have hG2 : ∀ w y, y ∈ Ω → ‖y - z‖ ^ 2 < δ ^ 2 + τ → dist w y < ε →
      -(δ₀ * ε) ≤ ‖w - z‖ ^ 2 - δ ^ 2 := by
    intro w y hyΩ _ hwy
    have h := hap w ε hε.le hε3 (hfar w y hyΩ hwy)
    have : 0 ≤ ‖w - y₀‖ ^ 2 / 2 := by positivity
    linarith
  have hG3 : ∀ w y, y ∈ Ω → ‖y - z‖ ^ 2 < δ ^ 2 + τ → dist w y < ε →
      ‖w - z‖ ^ 2 - δ ^ 2 ≤ 1 / (4 * M) := by
    intro w y _ hyD hwy
    have h1 : ‖w - z‖ ≤ ε + ‖y - z‖ := by
      have := norm_add_le (w - y) (y - z)
      rw [sub_add_sub_cancel] at this
      rw [dist_eq_norm] at hwy
      linarith
    have h2 : ‖w - z‖ ^ 2 ≤ (ε + ‖y - z‖) ^ 2 := by
      rw [sq, sq]; exact mul_self_le_mul_self (norm_nonneg _) h1
    have h3 : ‖y - z‖ ≤ ‖y - z‖ ^ 2 + 1 := by nlinarith [norm_nonneg (y - z)]
    have h4 : ε ^ 2 ≤ ε := by nlinarith
    have h5 : ε * K3 ≤ 1 / (8 * M) := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * M * K3)).1 hε7
      rw [le_div_iff₀ (by positivity)]
      linarith
    have h6 : 2 * ε * ‖y - z‖ ≤ 2 * ε * (δ ^ 2 + τ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : 1 / (8 * M) + 1 / (8 * M) = 1 / (4 * M) := by field_simp; ring
    nlinarith
  have hMa : M * (δ₀ * ε) ≤ 1 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < M * δ₀ + 1)).1 hε6
    nlinarith
  have hG4 : C ≤ c + A * (3 / 4 * τ) := by
    rw [hAτ]
    have := neg_abs_le c
    linarith
  have hG5 : ∀ w y, w ∉ Ω → y ∈ Ω → ‖y - z‖ ^ 2 < δ ^ 2 + τ → dist w y < ε →
      F w ≤ c - 2 * A * (δ₀ * ε) := by
    intro w y _ hyΩ hyD hwy
    have h1 := hclose y hyΩ hyD
    have h2 : dist w y₀ < r₀ := by
      have := dist_triangle w y y₀
      rw [dist_eq_norm y y₀] at this
      linarith
    have h3 := hF h2
    rw [Real.dist_eq] at h3
    have h4 : 2 * A * δ₀ * ε ≤ η₁ := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * A * δ₀ + 1)).1 hε5
      nlinarith
    have := (abs_lt.1 h3).2
    rw [hc]
    nlinarith
  -- the estimate at x
  by_cases hxΩ : x ∈ Ω
  · have hxr : ‖x - y₀‖ < r₁ := by rw [mem_ball, dist_eq_norm] at hx; exact hx
    have hr11 : r₁ ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
    have hr12 : r₁ ≤ τ / (2 * δ + 2) :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hr13 : r₁ ≤ η₁ / (A * (2 * δ + 1) + 1) :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have h1 : ‖x - z‖ < r₁ + δ := by
      have := norm_add_le (x - y₀) (y₀ - z)
      rw [sub_add_sub_cancel, hyz] at this
      linarith
    have h2 : ‖x - z‖ ^ 2 < (r₁ + δ) ^ 2 := by
      rw [sq, sq]; exact mul_self_lt_mul_self (norm_nonneg _) h1
    have h3 : (r₁ + δ) ^ 2 ≤ δ ^ 2 + (2 * δ + 1) * r₁ := by nlinarith
    have h4 : (2 * δ + 1) * r₁ < τ := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * δ + 2)).1 hr12
      nlinarith
    have hxD : ‖x - z‖ ^ 2 < δ ^ 2 + τ := by linarith
    have hcmp := bdry_compare hd hp hpd hC hu hout hδ z hA hτ.le (by positivity : 0 ≤ δ₀ * ε) hε
      hε₀ hε1 hMa hτM hG1 hG2 hG3 hG4 hG5 x hxΩ hxD
    have h5 := bpsi_le_t hM.le z δ x
    have h6 : A * bpsi z δ M x ≤ A * ((2 * δ + 1) * r₁) :=
      mul_le_mul_of_nonneg_left (by linarith) hA.le
    have h7 : A * ((2 * δ + 1) * r₁) ≤ η₁ := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < A * (2 * δ + 1) + 1)).1 hr13
      nlinarith
    rw [hc] at hcmp
    linarith
  · have h1 := hout ε hε x hxΩ
    have h2 : dist x y₀ < r₀ := lt_of_lt_of_le hx (min_le_left _ _)
    have h3 := hF h2
    rw [Real.dist_eq] at h3
    have := (abs_lt.1 h3).2
    linarith

/-! ## The boundary estimate -/

/-- **`ubar u ≤ F` at a boundary point with an exterior sphere.** -/
theorem ubar_le_bdry [Nontrivial (EuclSpace d)] (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε))
    (hout : ∀ ε > 0, ∀ x, x ∉ Ω → u ε x = F x)
    {y₀ : EuclSpace d} (hFc : ContinuousAt F y₀)
    {z₀ : EuclSpace d} {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hy₀z : ‖y₀ - z₀‖ = δ₀)
    (hext : ∀ x ∈ Ω, δ₀ ≤ ‖x - z₀‖) :
    ubar u y₀ ≤ F y₀ := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨ε₁, hε₁, r₁, hr₁, hb⟩ := bdry_step hd hp hpd hC hu hout hFc hδ₀ hy₀z hext
    (η₁ := η / 3) (by positivity)
  have h := ubar_le_of_bound u hC (S := Ioo 0 ε₁) (Ioo_mem_nhdsGT hε₁)
    (V := ball y₀ r₁) (b := F y₀ + 3 * (η / 3))
    (fun ε hε x hx => hb ε hε.1 hε.2 x hx) (ball_mem_nhds y₀ hr₁)
  linarith

end

end PLaplacian
