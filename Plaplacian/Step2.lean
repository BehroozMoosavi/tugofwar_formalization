/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Step2Prelim

@[expose] public section

/-! # The second step: no maximum with a nonzero gradient

Let `x` be a local maximum of `U - W` on `B(x, ρ) ⊆ O`, with `W = V - η V²`,
`U` semiconvex, `V` and `W` semiconcave, `U` satisfying the jet subsolution
inequality and `V` the jet supersolution inequality on `O`, and
`0 < 1 - 2ηV ≤ C_c` there. Then a lower support `q` of `U` at `x` is zero.

Suppose `q ≠ 0`, and put `κ = 2η(p - 1)(|q|/(2C_c))²`.

1. (`step2_point`) With tilts bounded by `δ_J`, Jensen's lemma for
   `Z = U - W - δ|· - x|²` gives a set of positive measure; it meets the
   Alexandrov sets of `U` and `-V` at a point `y₀`, with tilt `π`, where
   `a - c b = 2δ(y₀ - x) - π` and `A ≤ c B - 2η b ⊗ b + 2δ I`.
2. (`step2_chain`) The operator estimates give
   `2η(p - 1)|b|² ≤ 2δ(d + p - 2) + (p - 2) · 2L₀ · 12δ/Q`.
3. (`step2`) With `r` small against `ρ` and `|q|`, the gradient estimate gives
   `|c b| ≥ |q|/2` and `|b| ≥ |q|/(2C_c)`; with `δ` small against `κ`, the right
   side is at most `2κ/3` while the left is at least `κ`.
-/

open Set Topology Filter Metric MeasureTheory

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-! ## The point -/

set_option maxHeartbeats 800000 in
-- The extraction from Jensen's and Alexandrov's sets.
/-- **A point of Jensen's set where `U` and `V` are twice differentiable.** -/
theorem step2_point {U V : EuclSpace d → ℝ} {lam μ η : ℝ} (hlam : 0 ≤ lam) (hμ : 0 ≤ μ)
    (hU : SemiconvexWith lam U) (hV : SemiconvexWith lam (fun y => -V y))
    (hW : SemiconvexWith μ (fun y => -(V y - η * V y ^ 2)))
    {x : EuclSpace d} {ρ : ℝ}
    (hmax : ∀ y ∈ ball x ρ, U y - (V y - η * V y ^ 2) ≤ U x - (V x - η * V x ^ 2))
    {r δ δJ : ℝ} (hr0 : 0 < r) (hrρ : r < ρ) (hδ0 : 0 ≤ δ) (hδJ : 0 < δJ)
    (hδJr : 2 * δJ * r < δ * r ^ 2) :
    ∃ (y₀ a b : EuclSpace d) (A B : Bilin d) (π : EuclSpace d),
      ‖y₀ - x‖ < r ∧ ‖π‖ ≤ δJ ∧ PeanoAt U y₀ a A ∧ PeanoAt V y₀ b B ∧
      (∀ v, -(lam * ‖v‖ ^ 2) ≤ (A v) v) ∧ (∀ v, (B v) v ≤ lam * ‖v‖ ^ 2) ∧
      a - (1 - 2 * η * V y₀) • b = (2 * δ) • (y₀ - x) - π ∧
      QuadLE A ((1 - 2 * η * V y₀) • B - (2 * η) • rankOne b + (2 * δ) • idForm d) := by
  -- Jensen's lemma for Z = U - W - δ|· - x|²
  have hC0 : 0 ≤ lam + μ + 2 * δ := by positivity
  have hZconv : ConvexOn ℝ univ (fun y => (U y - (V y - η * V y ^ 2) - δ * ‖y - x‖ ^ 2)
      + (lam + μ + 2 * δ) / 2 * ‖y‖ ^ 2) :=
    convexOn_Z (W := fun y => V y - η * V y ^ 2) hU hW x
  have hsphere : ∀ y, ‖y - x‖ = r →
      (U y - (V y - η * V y ^ 2) - δ * ‖y - x‖ ^ 2) + 2 * δJ * r
        < U x - (V x - η * V x ^ 2) - δ * ‖x - x‖ ^ 2 := by
    intro y hy
    have hyb : y ∈ ball x ρ := by rw [mem_ball, dist_eq_norm, hy]; exact hrρ
    have h1 := hmax y hyb
    rw [hy, sub_self, norm_zero, zero_pow two_ne_zero, mul_zero, sub_zero]
    linarith
  have hpos := jensen_positive_measure
    (fun y => U y - (V y - η * V y ^ 2) - δ * ‖y - x‖ ^ 2) (lam + μ + 2 * δ) hC0 hZconv
    x x r δJ hr0 hδJ (mem_closedBall_self hr0.le) hsphere
  -- the Alexandrov sets
  have hAU := alexandrov (d := d) (fun y => U y + lam / 2 * ‖y‖ ^ 2) hU
  have hAV := alexandrov (d := d) (fun y => -V y + lam / 2 * ‖y‖ ^ 2) hV
  obtain ⟨y₀, hy₀K, ⟨gU, XU, hTU⟩, ⟨gV, XV, hTV⟩⟩ := exists_mem_pos_ae hpos (hAU.and hAV)
  obtain ⟨hy₀b, π, hπ, hπmax⟩ := hy₀K
  have hy₀x : ‖y₀ - x‖ < r := by rw [mem_ball, dist_eq_norm] at hy₀b; exact hy₀b
  -- the expansions of U and V
  have hPU : PeanoAt U y₀ (gU - lam • y₀) (XU - lam • idForm d) := by
    have h := peanoAt_sub_halfsq (peanoAt_of_twiceDiffAt hTU) lam
    intro ε hε
    obtain ⟨δ', hδ', hb⟩ := h ε hε
    refine ⟨δ', hδ', fun k hk => ?_⟩
    have := hb k hk
    simpa only [add_sub_cancel_right] using this
  have hPV : PeanoAt V y₀ (lam • y₀ - gV) (lam • idForm d - XV) := by
    have h := peanoAt_halfsq_sub (peanoAt_of_twiceDiffAt hTV) lam
    have e : ∀ y : EuclSpace d, lam / 2 * ‖y‖ ^ 2 - (-V y + lam / 2 * ‖y‖ ^ 2) = V y :=
      fun y => by ring
    intro ε hε
    obtain ⟨δ', hδ', hb⟩ := h ε hε
    refine ⟨δ', hδ', fun k hk => ?_⟩
    have := hb k hk
    simpa only [e] using this
  -- the Hessian bounds
  have hXU := convex_twiceDiff_nonneg hU hTU
  have hXV := convex_twiceDiff_nonneg hV hTV
  have hAv : ∀ v, -(lam * ‖v‖ ^ 2) ≤ ((XU - lam • idForm d) v) v := fun v => by
    simp only [sub_apply, smul_apply, smul_eq_mul, idForm_apply]
    linarith [hXU v]
  have hBv : ∀ v, ((lam • idForm d - XV) v) v ≤ lam * ‖v‖ ^ 2 := fun v => by
    simp only [sub_apply, smul_apply, smul_eq_mul, idForm_apply]
    linarith [hXV v]
  -- the expansion of F, and its maximum at y₀
  have hPF := peanoAt_add (peanoAt_sub hPU (peanoAt_cv hPV η)) (peanoAt_quadlin x y₀ π δ)
  have hFmax : ∀ᶠ z in 𝓝 y₀,
      (fun y => (U y - (V y - η * V y ^ 2)) + (-δ * ‖y - x‖ ^ 2 + inner ℝ π y)) z
        ≤ (fun y => (U y - (V y - η * V y ^ 2)) + (-δ * ‖y - x‖ ^ 2 + inner ℝ π y)) y₀ := by
    filter_upwards [isOpen_ball.mem_nhds hy₀b] with z hz
    have h1 : U z - (V z - η * V z ^ 2) - δ * ‖z - x‖ ^ 2 + inner ℝ π z
        ≤ U y₀ - (V y₀ - η * V y₀ ^ 2) - δ * ‖y₀ - x‖ ^ 2 + inner ℝ π y₀ :=
      hπmax z (ball_subset_closedBall hz)
    change (U z - (V z - η * V z ^ 2)) + (-δ * ‖z - x‖ ^ 2 + inner ℝ π z)
      ≤ (U y₀ - (V y₀ - η * V y₀ ^ 2)) + (-δ * ‖y₀ - x‖ ^ 2 + inner ℝ π y₀)
    linarith
  obtain ⟨hgrad, hhess⟩ := max_peano hPF hFmax
  refine ⟨y₀, gU - lam • y₀, lam • y₀ - gV, XU - lam • idForm d, lam • idForm d - XV, π,
    hy₀x, hπ, hPU, hPV, hAv, hBv, ?_, ?_⟩
  · exact sub_eq_zero.1 (by rw [← hgrad]; abel)
  · intro v
    have h := hhess v
    simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, idForm_apply] at h ⊢
    linarith

/-! ## The chain of operator estimates -/

set_option maxHeartbeats 800000 in
-- Five operator estimates combined.
/-- **The operator chain at the point.** -/
theorem step2_chain {p : ℝ} (hp : 2 ≤ p) {a b : EuclSpace d} {A B : Bilin d}
    {c η δ lam Cc Q : ℝ} (hη : 0 < η) (hc0 : 0 < c) (hcC : c ≤ Cc) (hlam : 0 ≤ lam)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hQ : 0 < Q)
    (hUi : 0 ≤ normPLapOf p a A) (hVi : normPLapOf p b B ≤ 0)
    (hquad : QuadLE A (c • B - (2 * η) • rankOne b + (2 * δ) • idForm d))
    (hAv : ∀ v, -(lam * ‖v‖ ^ 2) ≤ (A v) v) (hBv : ∀ v, (B v) v ≤ lam * ‖v‖ ^ 2)
    (hab : ‖a - c • b‖ ≤ 3 * δ) (hcb : Q / 2 ≤ ‖c • b‖) (ha0 : a ≠ 0) :
    2 * η * (p - 1) * ‖b‖ ^ 2
      ≤ 2 * δ * ((d : ℝ) + p - 2) + (p - 2) * (2 * (lam * (1 + Cc) + 1) * (12 * δ / Q)) := by
  have hcb0 : c • b ≠ 0 := by
    intro h; rw [h, norm_zero] at hcb; linarith
  have hb0 : b ≠ 0 := by
    intro h; apply hcb0; rw [h, smul_zero]
  have hp2 : 0 ≤ p - 2 := by linarith
  have hCc : 0 < Cc := lt_of_lt_of_le hc0 hcC
  set L0 := lam * (1 + Cc) + 1 with hL0
  have hL00 : 0 ≤ L0 := by positivity
  -- the quadratic bound on Y
  have hYv : ∀ v, |((c • B - (2 * η) • rankOne b + (2 * δ) • idForm d) v) v|
      ≤ L0 * ‖v‖ ^ 2 := by
    intro v
    have hv2 : 0 ≤ ‖v‖ ^ 2 := by positivity
    have hlo : -(L0 * ‖v‖ ^ 2) ≤ ((c • B - (2 * η) • rankOne b + (2 * δ) • idForm d) v) v := by
      have h1 := hquad v
      have h2 := hAv v
      have h3 : lam * ‖v‖ ^ 2 ≤ L0 * ‖v‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hv2
        rw [hL0]; nlinarith
      linarith
    have hhi : ((c • B - (2 * η) • rankOne b + (2 * δ) • idForm d) v) v ≤ L0 * ‖v‖ ^ 2 := by
      simp only [add_apply, sub_apply, smul_apply, smul_eq_mul, rankOne_apply, idForm_apply]
      have h1 : c * (B v) v ≤ c * (lam * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left (hBv v) hc0.le
      have h2 : c * (lam * ‖v‖ ^ 2) ≤ Cc * (lam * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hcC (by positivity)
      have h3 : 0 ≤ 2 * η * (inner ℝ b v * inner ℝ b v) := by
        have := mul_self_nonneg (inner ℝ b v)
        positivity
      have h4 : 2 * δ * ‖v‖ ^ 2 ≤ 1 * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) hv2
      have h5 : Cc * (lam * ‖v‖ ^ 2) + 1 * ‖v‖ ^ 2 ≤ L0 * ‖v‖ ^ 2 := by
        rw [hL0]; nlinarith
      linarith
    exact abs_le.2 ⟨hlo, hhi⟩
  -- the five estimates
  have e2 := normPLapOf_mono hp hquad a
  have e3 := (abs_le.1 (normPLapOf_dir hp ha0 hcb0 hL00 hYv)).2
  have e4 := normPLapOf_add_id (p := p) hcb0 (c • B - (2 * η) • rankOne b) (2 * δ)
  have e5 := normPLapOf_cv_strict hp hb0 hc0 hη.le hVi
  rw [e4] at e3
  -- the direction term
  have hdiv : 2 * ‖a - c • b‖ / ‖c • b‖ ≤ 12 * δ / Q := by
    rw [div_le_div_iff₀ (by positivity) hQ]
    have := mul_le_mul hab hcb (by positivity) (by positivity)
    nlinarith
  have hdirm : (p - 2) * (2 * L0 * (2 * ‖a - c • b‖ / ‖c • b‖))
      ≤ (p - 2) * (2 * L0 * (12 * δ / Q)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdiv (by positivity)) hp2
  linarith

/-! ## The second step -/

set_option maxHeartbeats 800000 in
-- The parameters, and the final arithmetic.
/-- **At a maximum of `U - ψ(V)`, the common gradient is zero.** -/
theorem step2 (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p) {U V : EuclSpace d → ℝ} {lam μ η Cc : ℝ}
    (hlam : 0 ≤ lam) (hμ : 0 ≤ μ) (hη : 0 < η)
    (hU : SemiconvexWith lam U) (hV : SemiconvexWith lam (fun y => -V y))
    (hW : SemiconvexWith μ (fun y => -(V y - η * V y ^ 2)))
    {O : Set (EuclSpace d)}
    (hUjet : ∀ y ∈ O, ∀ (q : EuclSpace d) (X : Bilin d), (q, X) ∈ SuperJet U y →
      q ≠ 0 → viscF p q X ≤ 0)
    (hVjet : ∀ y ∈ O, ∀ (q : EuclSpace d) (X : Bilin d), (q, X) ∈ SubJet V y →
      q ≠ 0 → 0 ≤ viscF p q X)
    (hc : ∀ y ∈ O, 0 < 1 - 2 * η * V y) (hCc : ∀ y ∈ O, 1 - 2 * η * V y ≤ Cc)
    {x : EuclSpace d} {ρ : ℝ} (hρ : 0 < ρ) (hball : ball x ρ ⊆ O)
    (hmax : ∀ y ∈ ball x ρ, U y - (V y - η * V y ^ 2) ≤ U x - (V x - η * V x ^ 2))
    {q : EuclSpace d}
    (hq : ∀ y, U x + inner ℝ q (y - x) - lam / 2 * ‖y - x‖ ^ 2 ≤ U y) :
    q = 0 := by
  by_contra hq0
  have hQ : 0 < ‖q‖ := norm_pos_iff.2 hq0
  have hxO : x ∈ O := hball (mem_ball_self hρ)
  have hCc0 : 0 < Cc := lt_of_lt_of_le (hc x hxO) (hCc x hxO)
  have hp2 : 0 ≤ p - 2 := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hD0 : 0 < (d : ℝ) + p - 2 := by linarith
  have hL00 : 0 ≤ lam * (1 + Cc) + 1 := by positivity
  set κ := 2 * η * (p - 1) * (‖q‖ / (2 * Cc)) ^ 2 with hκ
  have hκ0 : 0 < κ := by
    have : 0 < p - 1 := by linarith
    positivity
  -- the parameters
  set r := min (ρ / 4) (min 1 (‖q‖ / (2 * (lam + 2 * μ + 3)))) with hr
  have hr0 : 0 < r := lt_min (by positivity) (lt_min one_pos (by positivity))
  have hrρ : r ≤ ρ / 4 := min_le_left _ _
  have hr1 : r ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrq : r ≤ ‖q‖ / (2 * (lam + 2 * μ + 3)) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  set δ := min (1 / 2) (min (κ / (6 * ((d : ℝ) + p - 2)))
    (κ * ‖q‖ / (72 * ((p - 2) * (lam * (1 + Cc) + 1) + 1)))) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ κ / (6 * ((d : ℝ) + p - 2)) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ3 : δ ≤ κ * ‖q‖ / (72 * ((p - 2) * (lam * (1 + Cc) + 1) + 1)) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  set δJ := δ * r / 4 with hδJ
  have hδJ0 : 0 < δJ := by positivity
  have hδJr : 2 * δJ * r < δ * r ^ 2 := by
    rw [hδJ]
    have : 0 < δ * r ^ 2 := by positivity
    nlinarith
  -- the point
  obtain ⟨y₀, a, b, A, B, π, hy₀x, hπ, hPU, hPV, hAv, hBv, hgr, hquad⟩ :=
    step2_point hlam hμ hU hV hW hmax hr0 (by linarith) hδ0.le hδJ0 hδJr
  have hy₀O : y₀ ∈ O := hball (by rw [mem_ball, dist_eq_norm]; linarith)
  set c := 1 - 2 * η * V y₀ with hcdef
  have hc0 : 0 < c := hc y₀ hy₀O
  have hcC : c ≤ Cc := hCc y₀ hy₀O
  -- the gradient relation, in norm
  have hπn : ‖(2 * δ) • (y₀ - x) - π‖ ≤ 2 * δ * ‖y₀ - x‖ + δJ := by
    calc ‖(2 * δ) • (y₀ - x) - π‖ ≤ ‖(2 * δ) • (y₀ - x)‖ + ‖π‖ := norm_sub_le _ _
      _ = 2 * δ * ‖y₀ - x‖ + ‖π‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      _ ≤ 2 * δ * ‖y₀ - x‖ + δJ := by linarith
  have hδy : 2 * δ * ‖y₀ - x‖ ≤ 2 * δ * r :=
    mul_le_mul_of_nonneg_left hy₀x.le (by positivity)
  have hδJδ : δJ ≤ δ := by rw [hδJ]; nlinarith
  have hδJr' : δJ ≤ r := by rw [hδJ]; nlinarith
  have h2δr : 2 * δ * r ≤ r := by nlinarith
  have h2δ : 2 * δ * r ≤ 2 * δ := by nlinarith
  have hab_n : ‖a - c • b‖ ≤ 3 * δ := by rw [hgr]; linarith
  have hab_r : ‖a - c • b‖ ≤ 2 * r := by rw [hgr]; linarith
  -- the gradient estimate
  have hsupp := semiconvex_subJet_support hU (twiceDiffAt_of_peanoAt hPU).2
  have hgest := grad_est (W := fun y => V y - η * V y ^ 2) hlam hμ hρ hW hmax hq
    (by linarith : ‖y₀ - x‖ < ρ / 3) hsupp
  have hgest' : ‖a - q‖ ≤ (lam + 2 * μ) * r :=
    hgest.trans (mul_le_mul_of_nonneg_left hy₀x.le (by positivity))
  have hrq' : (lam + 2 * μ + 2) * r ≤ ‖q‖ / 2 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (lam + 2 * μ + 3))).1 hrq
    nlinarith
  -- the gradients are bounded below
  have hq_a : ‖q‖ ≤ ‖a - q‖ + ‖a‖ := by
    have := norm_sub_le a (a - q)
    rw [sub_sub_cancel] at this
    linarith
  have ha_cb : ‖a‖ ≤ ‖a - c • b‖ + ‖c • b‖ := by
    have := norm_sub_le (a - c • b) (-(c • b))
    rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at this
    exact this
  have hcb : ‖q‖ / 2 ≤ ‖c • b‖ := by linarith
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_sub, norm_neg] at hgest'
    linarith
  have hcbn : ‖c • b‖ = c * ‖b‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
  have hbq : ‖q‖ / (2 * Cc) ≤ ‖b‖ := by
    rw [div_le_iff₀ (by positivity)]
    have : c * ‖b‖ ≤ Cc * ‖b‖ := mul_le_mul_of_nonneg_right hcC (norm_nonneg _)
    linarith
  have hbκ : κ ≤ 2 * η * (p - 1) * ‖b‖ ^ 2 := by
    rw [hκ]
    have h1 : (‖q‖ / (2 * Cc)) ^ 2 ≤ ‖b‖ ^ 2 := by
      rw [sq, sq]; exact mul_self_le_mul_self (by positivity) hbq
    exact mul_le_mul_of_nonneg_left h1 (by have : 0 < p - 1 := (by linarith); positivity)
  -- the jet inequalities
  have hUi := hUjet y₀ hy₀O a A (twiceDiffAt_of_peanoAt hPU).1 ha0
  have hb0 : b ≠ 0 := by
    intro h; rw [h, smul_zero, norm_zero] at hcb; linarith
  have hVi := hVjet y₀ hy₀O b B (twiceDiffAt_of_peanoAt hPV).2 hb0
  rw [viscF_eq_neg] at hUi hVi
  -- the chain
  have hchain := step2_chain hp hη hc0 hcC hlam hδ0 hδ1 hQ (by linarith) (by linarith)
    hquad hAv hBv hab_n hcb ha0
  -- the right side is at most 2κ/3
  have hδD : 2 * δ * ((d : ℝ) + p - 2) ≤ κ / 3 := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 6 * ((d : ℝ) + p - 2))).1 hδ2
    linarith
  have hdir : (p - 2) * (2 * (lam * (1 + Cc) + 1) * (12 * δ / ‖q‖)) ≤ κ / 3 := by
    have h2 : (p - 2) * (2 * (lam * (1 + Cc) + 1) * (12 * δ / ‖q‖))
        = 24 * ((p - 2) * (lam * (1 + Cc) + 1) * δ) / ‖q‖ := by ring
    have h3 : δ * (72 * ((p - 2) * (lam * (1 + Cc) + 1) + 1)) ≤ κ * ‖q‖ :=
      (le_div_iff₀ (by positivity)).1 hδ3
    rw [h2, div_le_iff₀ hQ]
    have : 0 ≤ δ := hδ0.le
    linarith
  linarith

end

end PLaplacian
