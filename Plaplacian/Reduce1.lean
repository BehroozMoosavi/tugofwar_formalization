/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.QuarticJets

/-! # The reduction, part one: a strict global maximum

The theorem of sums is given a local maximum of
`u(x) - v(y) - ‖x - y‖⁴/(4α)` at `(x̂, ŷ)`, with `x̂ ≠ ŷ`. Writing `h₀ = x̂ - ŷ`
and `q = (‖h₀‖²/α) h₀` for the penalty gradient, translate, absorb the gradient,
and strictify:

  `ũ(ξ) = u(x̂ + ξ) - ⟪q, x̂ + ξ⟫ - K ‖ξ‖⁴ - c_u`,
  `ṽ(ζ) = v(ŷ + ζ) - ⟪q, ŷ + ζ⟫ + K ‖ζ‖⁴ - c_v`,

with the constants making both vanish at zero. With `P₀ = ½ S + ‖·‖²` (the
Taylor bound with `η = 1`), the function `Ψ(ξ, ζ) = ũ(ξ) - ṽ(ζ) - P₀(ξ - ζ)`
has a strict **global** maximum at the origin for `K` large:

* near zero, the local maximum and the Taylor bound give
  `Ψ ≤ -K(‖ξ‖⁴ + ‖ζ‖⁴)`;
* far from zero, at `t = ‖(ξ, ζ)‖ ≥ ρ`, the bounds on `u` and `v` give
  `Ψ ≤ B + 2‖q‖ t - K t⁴`, which the choice of `K` makes at most `-1`.

The term `‖q‖ + 1` in `K` also makes `ũ` and `-ṽ` bounded above, so that their
sup-convolutions are finite.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- The translated, strictified first function. -/
def uTilde (u : EuclSpace d → ℝ) (q xh : EuclSpace d) (K : ℝ) (ξ : EuclSpace d) : ℝ :=
  u (xh + ξ) - inner ℝ q (xh + ξ) - K * ‖ξ‖ ^ 4 - (u xh - inner ℝ q xh)

/-- The translated, strictified second function. -/
def vTilde (v : EuclSpace d → ℝ) (q yh : EuclSpace d) (K : ℝ) (ζ : EuclSpace d) : ℝ :=
  v (yh + ζ) - inner ℝ q (yh + ζ) + K * ‖ζ‖ ^ 4 - (v yh - inner ℝ q yh)

section defs

variable {u v : EuclSpace d → ℝ} {q xh yh : EuclSpace d} {K : ℝ}

theorem uTilde_zero : uTilde u q xh K 0 = 0 := by simp [uTilde]

theorem vTilde_zero : vTilde v q yh K 0 = 0 := by simp [vTilde]

/-- The difference, in terms of the original functions. -/
theorem uTilde_sub_vTilde (ξ ζ : EuclSpace d) :
    uTilde u q xh K ξ - vTilde v q yh K ζ
      = (u (xh + ξ) - v (yh + ζ) - inner ℝ q (ξ - ζ)) - (u xh - v yh)
        - K * (‖ξ‖ ^ 4 + ‖ζ‖ ^ 4) := by
  unfold uTilde vTilde
  rw [inner_add_right, inner_add_right, inner_sub_right]
  ring

end defs

/-- `t - t⁴ ≤ 1` for `t ≥ 0`. -/
theorem sub_pow_four_le_one {t : ℝ} (ht : 0 ≤ t) : t - t ^ 4 ≤ 1 := by
  rcases le_total t 1 with h | h
  · have : 0 ≤ t ^ 4 := by positivity
    linarith
  · have h3 : 1 ≤ t ^ 3 := one_le_pow₀ h
    have : t ≤ t ^ 4 := by
      calc t = t * 1 := (mul_one t).symm
        _ ≤ t * t ^ 3 := mul_le_mul_of_nonneg_left h3 ht
        _ = t ^ 4 := by ring
    linarith

section bounds

variable {u v : EuclSpace d → ℝ} {q xh yh : EuclSpace d} {K : ℝ}

/-- **`ũ` is bounded above.** -/
theorem bddAbove_uTilde (hK : ‖q‖ + 1 ≤ K) (hub : BddAbove (range u)) :
    BddAbove (range (uTilde u q xh K)) := by
  obtain ⟨SU, hSU⟩ := hub
  refine ⟨SU - inner ℝ q xh + ‖q‖ - (u xh - inner ℝ q xh), ?_⟩
  rintro _ ⟨ξ, rfl⟩
  unfold uTilde
  rw [inner_add_right]
  have h1 : u (xh + ξ) ≤ SU := hSU ⟨xh + ξ, rfl⟩
  have h2 : -inner ℝ q ξ ≤ ‖q‖ * ‖ξ‖ := by
    have := abs_real_inner_le_norm q ξ
    rw [abs_le] at this
    linarith [this.1]
  have h3 := sub_pow_four_le_one (norm_nonneg ξ)
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have h4 : 0 ≤ ‖ξ‖ ^ 4 := by positivity
  have h5 : ‖q‖ * ‖ξ‖ - K * ‖ξ‖ ^ 4 ≤ ‖q‖ := by
    have e1 : ‖q‖ * ‖ξ‖ - K * ‖ξ‖ ^ 4 ≤ ‖q‖ * ‖ξ‖ - ‖q‖ * ‖ξ‖ ^ 4 := by
      have : ‖q‖ * ‖ξ‖ ^ 4 ≤ K * ‖ξ‖ ^ 4 :=
        mul_le_mul_of_nonneg_right (by linarith) h4
      linarith
    have e2 : ‖q‖ * ‖ξ‖ - ‖q‖ * ‖ξ‖ ^ 4 ≤ ‖q‖ * 1 := by
      have := mul_le_mul_of_nonneg_left h3 hq0
      linarith
    linarith
  linarith

/-- **`-ṽ` is bounded above.** -/
theorem bddAbove_neg_vTilde (hK : ‖q‖ + 1 ≤ K) (hvb : BddBelow (range v)) :
    BddAbove (range (fun ζ => -vTilde v q yh K ζ)) := by
  obtain ⟨IV, hIV⟩ := hvb
  refine ⟨-IV + inner ℝ q yh + ‖q‖ + (v yh - inner ℝ q yh), ?_⟩
  rintro _ ⟨ζ, rfl⟩
  change -vTilde v q yh K ζ ≤ _
  unfold vTilde
  rw [inner_add_right]
  have h1 : IV ≤ v (yh + ζ) := hIV ⟨yh + ζ, rfl⟩
  have h2 : inner ℝ q ζ ≤ ‖q‖ * ‖ζ‖ := real_inner_le_norm q ζ
  have h3 := sub_pow_four_le_one (norm_nonneg ζ)
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  have h4 : 0 ≤ ‖ζ‖ ^ 4 := by positivity
  have h5 : ‖q‖ * ‖ζ‖ - K * ‖ζ‖ ^ 4 ≤ ‖q‖ := by
    have e1 : ‖q‖ * ‖ζ‖ - K * ‖ζ‖ ^ 4 ≤ ‖q‖ * ‖ζ‖ - ‖q‖ * ‖ζ‖ ^ 4 := by
      have : ‖q‖ * ‖ζ‖ ^ 4 ≤ K * ‖ζ‖ ^ 4 :=
        mul_le_mul_of_nonneg_right (by linarith) h4
      linarith
    have e2 : ‖q‖ * ‖ζ‖ - ‖q‖ * ‖ζ‖ ^ 4 ≤ ‖q‖ * 1 := by
      have := mul_le_mul_of_nonneg_left h3 hq0
      linarith
    linarith
  linarith

/-- **`ũ` is upper semicontinuous.** -/
theorem usc_uTilde (hu : UpperSemicontinuous u) :
    UpperSemicontinuous (uTilde u q xh K) := by
  have h1 : UpperSemicontinuous (fun ξ : EuclSpace d => u (xh + ξ)) :=
    hu.comp (continuous_const.add continuous_id)
  have h2 : UpperSemicontinuous (fun ξ : EuclSpace d =>
      -inner ℝ q (xh + ξ) - K * ‖ξ‖ ^ 4 - (u xh - inner ℝ q xh)) := by
    apply Continuous.upperSemicontinuous; fun_prop
  have heq : uTilde u q xh K = fun ξ => u (xh + ξ)
      + (-inner ℝ q (xh + ξ) - K * ‖ξ‖ ^ 4 - (u xh - inner ℝ q xh)) := by
    funext ξ; unfold uTilde; ring
  rw [heq]
  exact h1.add h2

/-- **`-ṽ` is upper semicontinuous.** -/
theorem usc_neg_vTilde (hv : LowerSemicontinuous v) :
    UpperSemicontinuous (fun ζ => -vTilde v q yh K ζ) := by
  have h1 : UpperSemicontinuous (fun ζ : EuclSpace d => -v (yh + ζ)) :=
    hv.neg.comp (continuous_const.add continuous_id)
  have h2 : UpperSemicontinuous (fun ζ : EuclSpace d =>
      inner ℝ q (yh + ζ) - K * ‖ζ‖ ^ 4 + (v yh - inner ℝ q yh)) := by
    apply Continuous.upperSemicontinuous; fun_prop
  have heq : (fun ζ => -vTilde v q yh K ζ) = fun ζ => -v (yh + ζ)
      + (inner ℝ q (yh + ζ) - K * ‖ζ‖ ^ 4 + (v yh - inner ℝ q yh)) := by
    funext ζ; unfold vTilde; ring
  rw [heq]
  exact h1.add h2

end bounds

section strict

variable {u v : EuclSpace d → ℝ} {α : ℝ} {xh yh : EuclSpace d}

/-- **The local bound**: near the origin, the local maximum and the Taylor bound
of the penalty give the reduced inequality. -/
theorem local_bound (hα : 0 < α)
    (hmax : IsLocalMax (fun z : EuclSpace d × EuclSpace d =>
      u z.1 - v z.2 - ‖z.1 - z.2‖ ^ 4 / (4 * α)) (xh, yh)) :
    ∃ ρ > 0, ∀ ξ ζ : EuclSpace d, ‖(ξ, ζ)‖ < ρ →
      u (xh + ξ) - v (yh + ζ)
        - inner ℝ ((‖xh - yh‖ ^ 2 / α) • (xh - yh)) (ξ - ζ)
        - penP (1 / 2) 1 α (xh - yh) (ξ - ζ) ≤ u xh - v yh := by
  have hT := penalty_upper hα (xh - yh) (one_pos : (0 : ℝ) < 1)
  have hm : Tendsto (fun w : EuclSpace d × EuclSpace d => (xh + w.1, yh + w.2))
      (𝓝 0) (𝓝 (xh, yh)) := by
    have h0 : Continuous (fun w : EuclSpace d × EuclSpace d => (xh + w.1, yh + w.2)) := by
      fun_prop
    have := h0.tendsto 0
    simpa using this
  have hk : Tendsto (fun w : EuclSpace d × EuclSpace d => w.1 - w.2) (𝓝 0) (𝓝 0) := by
    have h0 : Continuous (fun w : EuclSpace d × EuclSpace d => w.1 - w.2) := by fun_prop
    have := h0.tendsto 0
    simpa using this
  have hev : ∀ᶠ w in 𝓝 (0 : EuclSpace d × EuclSpace d),
      u (xh + w.1) - v (yh + w.2)
        - inner ℝ ((‖xh - yh‖ ^ 2 / α) • (xh - yh)) (w.1 - w.2)
        - penP (1 / 2) 1 α (xh - yh) (w.1 - w.2) ≤ u xh - v yh := by
    filter_upwards [hm.eventually hmax, hk.eventually hT] with w h1 h2
    change u (xh + w.1) - v (yh + w.2) - ‖xh + w.1 - (yh + w.2)‖ ^ 4 / (4 * α)
      ≤ u xh - v yh - ‖xh - yh‖ ^ 4 / (4 * α) at h1
    have e : xh + w.1 - (yh + w.2) = (xh - yh) + (w.1 - w.2) := by abel
    rw [e] at h1
    unfold penP
    linarith
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  exact ⟨ρ, hρ, fun ξ ζ h => hball (by rwa [dist_zero_right])⟩

/-- `‖w‖⁴ ≤ ‖w.1‖⁴ + ‖w.2‖⁴` on the product. -/
theorem norm_pow_four_le_sum (w : EuclSpace d × EuclSpace d) :
    ‖w‖ ^ 4 ≤ ‖w.1‖ ^ 4 + ‖w.2‖ ^ 4 := by
  have hmax : ‖w‖ ≤ max ‖w.1‖ ‖w.2‖ :=
    norm_prod_le_iff.2 ⟨le_max_left _ _, le_max_right _ _⟩
  have h1 : 0 ≤ ‖w.1‖ ^ 4 := by positivity
  have h2 : 0 ≤ ‖w.2‖ ^ 4 := by positivity
  rcases le_total ‖w.1‖ ‖w.2‖ with h | h
  · rw [max_eq_right h] at hmax
    have := pow_le_pow_left₀ (norm_nonneg w) hmax 4
    linarith
  · rw [max_eq_left h] at hmax
    have := pow_le_pow_left₀ (norm_nonneg w) hmax 4
    linarith

/-- Off the origin, the sum of fourth powers is positive. -/
theorem sum_pow_four_pos {w : EuclSpace d × EuclSpace d} (hw : w ≠ 0) :
    0 < ‖w.1‖ ^ 4 + ‖w.2‖ ^ 4 := by
  by_contra hc
  push Not at hc
  have h1 : 0 ≤ ‖w.1‖ ^ 4 := by positivity
  have h2 : 0 ≤ ‖w.2‖ ^ 4 := by positivity
  have e1 : ‖w.1‖ ^ 4 = 0 := by linarith
  have e2 : ‖w.2‖ ^ 4 = 0 := by linarith
  have f1 : w.1 = 0 := norm_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 e1)
  have f2 : w.2 = 0 := norm_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 e2)
  exact hw (Prod.ext f1 f2)

/-- **The strict global maximum.** -/
theorem exists_K_strict (hα : 0 < α) (hub : BddAbove (range u))
    (hvb : BddBelow (range v))
    (hmax : IsLocalMax (fun z : EuclSpace d × EuclSpace d =>
      u z.1 - v z.2 - ‖z.1 - z.2‖ ^ 4 / (4 * α)) (xh, yh)) :
    ∃ K : ℝ, ‖(‖xh - yh‖ ^ 2 / α) • (xh - yh)‖ + 1 ≤ K ∧
      ∀ w : EuclSpace d × EuclSpace d, w ≠ 0 →
        uTilde u ((‖xh - yh‖ ^ 2 / α) • (xh - yh)) xh K w.1
          - vTilde v ((‖xh - yh‖ ^ 2 / α) • (xh - yh)) yh K w.2
          - penP (1 / 2) 1 α (xh - yh) (w.1 - w.2) < 0 := by
  set q := (‖xh - yh‖ ^ 2 / α) • (xh - yh) with hqdef
  obtain ⟨ρ, hρ, hloc⟩ := local_bound hα hmax
  obtain ⟨SU, hSU⟩ := hub
  obtain ⟨IV, hIV⟩ := hvb
  have hU : ∀ x, u x ≤ SU := fun x => hSU ⟨x, rfl⟩
  have hV : ∀ y, IV ≤ v y := fun y => hIV ⟨y, rfl⟩
  set B := SU - IV - (u xh - v yh) with hBdef
  have hB : 0 ≤ B := by have := hU xh; have := hV yh; rw [hBdef]; linarith
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg q
  set K := (B + 1) / ρ ^ 4 + 2 * ‖q‖ / ρ ^ 3 + ‖q‖ + 1 with hKdef
  have hK1 : ‖q‖ + 1 ≤ K := by
    have : 0 ≤ (B + 1) / ρ ^ 4 := by positivity
    have : 0 ≤ 2 * ‖q‖ / ρ ^ 3 := by positivity
    rw [hKdef]; linarith
  have hKpos : 0 < K := by linarith
  refine ⟨K, hK1, fun w hw => ?_⟩
  rw [uTilde_sub_vTilde]
  have hP0 : 0 ≤ penP (1 / 2) 1 α (xh - yh) (w.1 - w.2) :=
    penP_nonneg (by norm_num) zero_le_one hα _
  have hw4 := sum_pow_four_pos hw
  by_cases hsmall : ‖w‖ < ρ
  · -- near the origin
    have h1 := hloc w.1 w.2 hsmall
    have := mul_pos hKpos hw4
    linarith
  · -- far from the origin
    push Not at hsmall
    set t := ‖w‖ with htdef
    have ht0 : 0 < t := lt_of_lt_of_le hρ hsmall
    have hn1 : ‖w.1‖ ≤ t := norm_fst_le w
    have hn2 : ‖w.2‖ ≤ t := norm_snd_le w
    have hinner : -inner ℝ q (w.1 - w.2) ≤ 2 * ‖q‖ * t := by
      have h1 : -inner ℝ q (w.1 - w.2) ≤ ‖q‖ * ‖w.1 - w.2‖ := by
        have := abs_real_inner_le_norm q (w.1 - w.2)
        rw [abs_le] at this
        linarith [this.1]
      have h2 : ‖w.1 - w.2‖ ≤ 2 * t := by
        have := norm_sub_le w.1 w.2
        linarith
      have := mul_le_mul_of_nonneg_left h2 hq0
      linarith
    have hfour := norm_pow_four_le_sum w
    have hKt : K * t ^ 4 ≤ K * (‖w.1‖ ^ 4 + ‖w.2‖ ^ 4) :=
      mul_le_mul_of_nonneg_left hfour hKpos.le
    -- K t⁴ ≥ B + 1 + 2 ‖q‖ t
    have hρ3 : ρ ^ 3 ≤ t ^ 3 := pow_le_pow_left₀ hρ.le hsmall 3
    have hKρ : (B + 1) / ρ + 2 * ‖q‖ ≤ K * ρ ^ 3 := by
      have e : K * ρ ^ 3 = (B + 1) / ρ + 2 * ‖q‖ + (‖q‖ + 1) * ρ ^ 3 := by
        rw [hKdef]; field_simp; ring
      have : 0 ≤ (‖q‖ + 1) * ρ ^ 3 := by positivity
      linarith
    have hA : K * ρ ^ 3 * t ≤ K * t ^ 4 := by
      have : K * ρ ^ 3 ≤ K * t ^ 3 := mul_le_mul_of_nonneg_left hρ3 hKpos.le
      have e : K * t ^ 4 = K * t ^ 3 * t := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right this ht0.le
    have hB1 : B + 1 ≤ (B + 1) / ρ * t := by
      have : (B + 1) / ρ * ρ = B + 1 := div_mul_cancel₀ _ hρ.ne'
      have h2 : (B + 1) / ρ * ρ ≤ (B + 1) / ρ * t :=
        mul_le_mul_of_nonneg_left hsmall (by positivity)
      linarith
    have hC : ((B + 1) / ρ + 2 * ‖q‖) * t ≤ K * ρ ^ 3 * t :=
      mul_le_mul_of_nonneg_right hKρ ht0.le
    have hu1 := hU (xh + w.1)
    have hv1 := hV (yh + w.2)
    nlinarith

end strict

end

end PLaplacian
