/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.OpEst

/-! # Tools for the second step

At a point `y₀` where `U` and `V` are twice differentiable, the function
`F(y) = U(y) - W(y) - δ‖y - x‖² + ⟪π, y⟫` has a local maximum. This file
supplies what reading off its first- and second-order conditions needs:

1. Peano expansions add and subtract;
2. `-δ‖y - x‖² + ⟪π, y⟫` has the exact expansion
   `(π - 2δ(y₀ - x), -2δ I)`;
3. at a local maximum, an expansion has gradient zero and Hessian `≤ 0`;
4. `Z = U - W - δ‖· - x‖²` is semiconvex with constant `λ + μ + 2δ`, since
   `δ‖y‖² - δ‖y - x‖²` is affine — the global semiconvexity Jensen's lemma
   needs;
5. a set of positive measure meets every set of full measure.
-/

open Set Topology Filter Metric MeasureTheory

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-! ## Peano algebra -/

theorem peanoAt_add {f g : EuclSpace d → ℝ} {x gf gg : EuclSpace d} {Xf Xg : Bilin d}
    (hf : PeanoAt f x gf Xf) (hg : PeanoAt g x gg Xg) :
    PeanoAt (fun y => f y + g y) x (gf + gg) (Xf + Xg) := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, h1⟩ := hf (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, h2⟩ := hg (ε / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun k hk => ?_⟩
  have a1 := h1 k (lt_of_lt_of_le hk (min_le_left _ _))
  have a2 := h2 k (lt_of_lt_of_le hk (min_le_right _ _))
  change |(f (x + k) + g (x + k)) - (f x + g x) - inner ℝ (gf + gg) k
    - 1 / 2 * ((Xf + Xg) k) k| ≤ ε * ‖k‖ ^ 2
  rw [inner_add_left, add_apply, add_apply]
  obtain ⟨b1, b2⟩ := abs_le.1 a1
  obtain ⟨c1, c2⟩ := abs_le.1 a2
  rw [abs_le]
  constructor <;> linarith

theorem peanoAt_sub {f g : EuclSpace d → ℝ} {x gf gg : EuclSpace d} {Xf Xg : Bilin d}
    (hf : PeanoAt f x gf Xf) (hg : PeanoAt g x gg Xg) :
    PeanoAt (fun y => f y - g y) x (gf - gg) (Xf - Xg) := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, h1⟩ := hf (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, h2⟩ := hg (ε / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun k hk => ?_⟩
  have a1 := h1 k (lt_of_lt_of_le hk (min_le_left _ _))
  have a2 := h2 k (lt_of_lt_of_le hk (min_le_right _ _))
  change |(f (x + k) - g (x + k)) - (f x - g x) - inner ℝ (gf - gg) k
    - 1 / 2 * ((Xf - Xg) k) k| ≤ ε * ‖k‖ ^ 2
  rw [inner_sub_left, sub_apply, sub_apply]
  obtain ⟨b1, b2⟩ := abs_le.1 a1
  obtain ⟨c1, c2⟩ := abs_le.1 a2
  rw [abs_le]
  constructor <;> linarith

/-- **The exact expansion of the penalty and the tilt.** -/
theorem peanoAt_quadlin (x y₀ π : EuclSpace d) (δ : ℝ) :
    PeanoAt (fun y => -δ * ‖y - x‖ ^ 2 + inner ℝ π y) y₀
      (π - (2 * δ) • (y₀ - x)) ((-2 * δ) • idForm d) := by
  intro ε hε
  refine ⟨1, one_pos, fun k _ => ?_⟩
  change |(-δ * ‖y₀ + k - x‖ ^ 2 + inner ℝ π (y₀ + k)) - (-δ * ‖y₀ - x‖ ^ 2 + inner ℝ π y₀)
    - inner ℝ (π - (2 * δ) • (y₀ - x)) k - 1 / 2 * (((-2 * δ) • idForm d) k) k|
      ≤ ε * ‖k‖ ^ 2
  have e : y₀ + k - x = (y₀ - x) + k := by abel
  rw [e, norm_add_sq_real, inner_add_right, inner_sub_left π ((2 * δ) • (y₀ - x)) k,
    real_inner_smul_left, smul_apply, smul_apply, smul_eq_mul, idForm_apply]
  have key : (-δ * (‖y₀ - x‖ ^ 2 + 2 * inner ℝ (y₀ - x) k + ‖k‖ ^ 2)
      + (inner ℝ π y₀ + inner ℝ π k)) - (-δ * ‖y₀ - x‖ ^ 2 + inner ℝ π y₀)
      - (inner ℝ π k - 2 * δ * inner ℝ (y₀ - x) k) - 1 / 2 * (-2 * δ * ‖k‖ ^ 2) = 0 := by
    ring
  rw [key, abs_zero]
  positivity

/-! ## The conditions at a maximum -/

/-- **At a local maximum, an expansion has gradient zero and Hessian `≤ 0`.** -/
theorem max_peano {F : EuclSpace d → ℝ} {y g : EuclSpace d} {G : Bilin d}
    (hF : PeanoAt F y g G) (hmax : ∀ᶠ z in 𝓝 y, F z ≤ F y) :
    g = 0 ∧ ∀ v, (G v) v ≤ 0 := by
  obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff.1 hmax
  -- the lower expansion along t w
  have key : ∀ (w : EuclSpace d) (ε : ℝ), 0 < ε → ∃ t > 0,
      t * inner ℝ g w + 1 / 2 * t ^ 2 * (G w) w - ε * t ^ 2 * ‖w‖ ^ 2 ≤ 0 ∧
      ∀ s, 0 < s → s ≤ t →
        s * inner ℝ g w + 1 / 2 * s ^ 2 * (G w) w - ε * s ^ 2 * ‖w‖ ^ 2 ≤ 0 := by
    intro w ε hε
    obtain ⟨δ, hδ, hb⟩ := hF ε hε
    set t := min δ r₀ / (2 * (‖w‖ + 1)) with ht
    have ht0 : 0 < t := by positivity
    have hs : ∀ s, 0 < s → s ≤ t →
        s * inner ℝ g w + 1 / 2 * s ^ 2 * (G w) w - ε * s ^ 2 * ‖w‖ ^ 2 ≤ 0 := by
      intro s hs0 hst
      have hsw : ‖s • w‖ < min δ r₀ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
        have h1 : s * (2 * (‖w‖ + 1)) ≤ min δ r₀ := (le_div_iff₀ (by positivity)).1 hst
        have hm : 0 < min δ r₀ := lt_min hδ hr₀
        nlinarith [norm_nonneg w]
      have a1 := hb (s • w) (lt_of_lt_of_le hsw (min_le_left _ _))
      have a2 : F (y + s • w) ≤ F y := hball (by
        rw [dist_eq_norm]
        have e : y + s • w - y = s • w := by abel
        rw [e]; exact lt_of_lt_of_le hsw (min_le_right _ _))
      have hGs : (G (s • w)) (s • w) = s * (s * (G w) w) := by
        simp only [map_smul, smul_apply, smul_eq_mul]
      rw [real_inner_smul_right, hGs, norm_smul, Real.norm_eq_abs, abs_of_pos hs0] at a1
      have := (abs_le.1 a1).1
      nlinarith
    exact ⟨t, ht0, hs t ht0 le_rfl, hs⟩
  -- the gradient vanishes
  have hg : g = 0 := by
    by_contra hne
    have hgn : 0 < ‖g‖ := norm_pos_iff.2 hne
    obtain ⟨t, ht0, _, hs⟩ := key g 1 one_pos
    rw [real_inner_self_eq_norm_sq] at hs
    set s := min t (‖g‖ ^ 2 / (2 * (|(G g) g| + ‖g‖ ^ 2 + 1))) with hsdef
    have hs0 : 0 < s := lt_min ht0 (by positivity)
    have h1 := hs s hs0 (min_le_left _ _)
    have h2 : s ≤ ‖g‖ ^ 2 / (2 * (|(G g) g| + ‖g‖ ^ 2 + 1)) := min_le_right _ _
    have h3 : s * (2 * (|(G g) g| + ‖g‖ ^ 2 + 1)) ≤ ‖g‖ ^ 2 := (le_div_iff₀ (by positivity)).1 h2
    have h4' : -((G g) g) ≤ |(G g) g| := neg_le_abs _
    have h45 : -(1 / 2 * s ^ 2 * (G g) g) ≤ s ^ 2 * |(G g) g| := by
      have := mul_le_mul_of_nonneg_left h4' (sq_nonneg s)
      have h0 : 0 ≤ s ^ 2 * |(G g) g| := by positivity
      linarith
    -- s ‖g‖² ≤ s² (‖g‖² + |G g g|), so ‖g‖² ≤ s (‖g‖² + |G g g|) < ‖g‖²
    have h5 : s * ‖g‖ ^ 2 ≤ s ^ 2 * (‖g‖ ^ 2 + |(G g) g|) := by linarith
    have h6 : ‖g‖ ^ 2 ≤ s * (‖g‖ ^ 2 + |(G g) g|) := by
      have := h5
      have hs2 : s ^ 2 = s * s := by ring
      rw [hs2, mul_assoc] at this
      exact le_of_mul_le_mul_left this hs0
    have hg2 : 0 < ‖g‖ ^ 2 := pow_pos hgn 2
    nlinarith [abs_nonneg ((G g) g)]
  refine ⟨hg, fun v => ?_⟩
  by_contra hpos
  push Not at hpos
  set κ := (G v) v with hκ
  have hv : v ≠ 0 := by
    intro h; rw [h] at hκ; simp at hκ; linarith
  set ε := κ / (4 * (‖v‖ ^ 2 + 1)) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨t, ht0, h1, _⟩ := key v ε hε
  rw [hg, inner_zero_left, mul_zero, zero_add] at h1
  have h2 : ε * ‖v‖ ^ 2 ≤ κ / 4 := by
    rw [hεdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg ‖v‖]
  have h3 : t ^ 2 * (1 / 2 * κ - ε * ‖v‖ ^ 2) ≤ 0 := by nlinarith
  have h4 : 0 < t ^ 2 * (1 / 2 * κ - ε * ‖v‖ ^ 2) := by
    apply mul_pos (by positivity); linarith
  linarith

/-! ## Semiconvexity of `Z` -/

/-- An affine function is convex. -/
theorem convexOn_affine (x : EuclSpace d) (c c₀ : ℝ) :
    ConvexOn ℝ univ (fun y : EuclSpace d => c * inner ℝ x y + c₀) := by
  refine ⟨convex_univ, fun y₁ _ y₂ _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, inner_add_right, real_inner_smul_right]
  have : c₀ = a * c₀ + b * c₀ := by rw [← add_mul, hab, one_mul]
  nlinarith

/-- **`U - W - δ‖· - x‖²` is semiconvex**, with constant `λ + μ + 2δ`. -/
theorem convexOn_Z {U W : EuclSpace d → ℝ} {lam μ δ : ℝ} (hU : SemiconvexWith lam U)
    (hW : SemiconvexWith μ (fun y => -W y)) (x : EuclSpace d) :
    ConvexOn ℝ univ (fun y => (U y - W y - δ * ‖y - x‖ ^ 2)
      + (lam + μ + 2 * δ) / 2 * ‖y‖ ^ 2) := by
  have h := (hU.add hW).add (convexOn_affine x (2 * δ) (-δ * ‖x‖ ^ 2))
  refine h.congr fun y _ => ?_
  simp only [Pi.add_apply]
  have e : ‖y - x‖ ^ 2 = ‖y‖ ^ 2 - 2 * inner ℝ x y + ‖x‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm]
  rw [e]
  ring

/-! ## Positive measure meets full measure -/

theorem exists_mem_pos_ae {K : Set (EuclSpace d)} {P : EuclSpace d → Prop}
    (hK : 0 < volume K) (hP : ∀ᵐ y ∂(volume : Measure (EuclSpace d)), P y) :
    ∃ y ∈ K, P y := by
  by_contra hcon
  push Not at hcon
  have hsub : K ⊆ {y | ¬ P y} := fun y hy => hcon y hy
  have h0 : volume K = 0 := measure_mono_null hsub (ae_iff.1 hP)
  exact (ne_of_gt hK) h0

end

end PLaplacian
