/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.FormCompact

@[expose] public section

/-! # Superjet algebra, and the jets of the quartic

The reduction strictifies the maximum by subtracting `K ‖ξ‖⁴`, and the assembly
must add it back, at points approaching the base point. This file supplies the
superjet counterparts of the subjet rules, and the jets of `‖· - c‖⁴`.

## The quartic

Squaring `‖x + k‖² = ‖x‖² + 2⟪x, k⟫ + ‖k‖²` gives

  `‖x + k‖⁴ = ‖x‖⁴ + ⟪4‖x‖² x, k⟫ + (2‖x‖²‖k‖² + 4⟪x, k⟫²) + R(k)`,

whose quadratic part is at most `6 ‖x‖² ‖k‖²` and whose remainder `R` is the
`penR` of the penalty file with `α = 1/4`, so `eventually_penR_le` bounds it
already. Hence `(4‖x - c‖² (x - c), 12 ‖x - c‖² I)` is a superjet of `‖· - c‖⁴`
at `x`, and its negation a subjet of `-‖· - c‖⁴`. The form `12 ‖x - c‖² I`
tends to zero as `x → c`, which is what lets the jets pass to the limit.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



section rules

variable {f g : EuclSpace d → ℝ} {x q₁ q₂ : EuclSpace d} {X₁ X₂ : Bilin d}

/-- **Superjets add.** -/
theorem superJet_add (h₁ : (q₁, X₁) ∈ SuperJet f x) (h₂ : (q₂, X₂) ∈ SuperJet g x) :
    (q₁ + q₂, X₁ + X₂) ∈ SuperJet (fun y => f y + g y) x := by
  intro η hη
  filter_upwards [h₁ (η / 2) (by positivity), h₂ (η / 2) (by positivity)]
    with y hy₁ hy₂
  change f y ≤ f x + inner ℝ q₁ (y - x) + (1 / 2) * (X₁ (y - x)) (y - x)
    + η / 2 * ‖y - x‖ ^ 2 at hy₁
  change g y ≤ g x + inner ℝ q₂ (y - x) + (1 / 2) * (X₂ (y - x)) (y - x)
    + η / 2 * ‖y - x‖ ^ 2 at hy₂
  change f y + g y ≤ f x + g x + inner ℝ (q₁ + q₂) (y - x)
    + (1 / 2) * ((X₁ + X₂) (y - x)) (y - x) + η * ‖y - x‖ ^ 2
  rw [inner_add_left, add_form_apply]
  linarith

/-- **Superjets translate.** -/
theorem superJet_comp_add (c : EuclSpace d) (h : (q₁, X₁) ∈ SuperJet f (x + c)) :
    (q₁, X₁) ∈ SuperJet (fun y => f (y + c)) x := by
  intro η hη
  have hT : Tendsto (fun y : EuclSpace d => y + c) (𝓝 x) (𝓝 (x + c)) :=
    (continuous_id.add continuous_const).tendsto x
  filter_upwards [hT.eventually (h η hη)] with y hy
  change f (y + c) ≤ f (x + c) + inner ℝ q₁ (y + c - (x + c))
    + (1 / 2) * (X₁ (y + c - (x + c))) (y + c - (x + c))
    + η * ‖y + c - (x + c)‖ ^ 2 at hy
  change f (y + c) ≤ f (x + c) + inner ℝ q₁ (y - x) + (1 / 2) * (X₁ (y - x)) (y - x)
    + η * ‖y - x‖ ^ 2
  have e : y + c - (x + c) = y - x := by abel
  rw [e] at hy
  exact hy

/-- Adding an affine function shifts a superjet's gradient. -/
theorem superJet_add_affine (h : (q₁, X₁) ∈ SuperJet f x) (p : EuclSpace d) (c : ℝ) :
    (q₁ + p, X₁) ∈ SuperJet (fun y => f y + inner ℝ p y + c) x := by
  intro η hη
  filter_upwards [h η hη] with y hy
  change f y ≤ f x + inner ℝ q₁ (y - x) + (1 / 2) * (X₁ (y - x)) (y - x)
    + η * ‖y - x‖ ^ 2 at hy
  change f y + inner ℝ p y + c ≤ f x + inner ℝ p x + c + inner ℝ (q₁ + p) (y - x)
    + (1 / 2) * (X₁ (y - x)) (y - x) + η * ‖y - x‖ ^ 2
  have e : inner ℝ p (y - x) = inner ℝ p y - inner ℝ p x := inner_sub_right _ _ _
  rw [inner_add_left]
  linarith

end rules

/-! ## The quartic -/

/-- **The exact expansion of the quartic.** -/
theorem quartic_expand (x k : EuclSpace d) :
    ‖x + k‖ ^ 4 = ‖x‖ ^ 4 + inner ℝ ((4 * ‖x‖ ^ 2) • x) k
      + (2 * ‖x‖ ^ 2 * ‖k‖ ^ 2 + 4 * inner ℝ x k ^ 2) + penR (1 / 4) x k := by
  have hsq : ‖x + k‖ ^ 4 = (‖x + k‖ ^ 2) ^ 2 := by ring
  rw [hsq, norm_add_sq_real, real_inner_smul_left]
  unfold penR
  ring

/-- The quadratic part of the quartic is at most `6 ‖x‖² ‖k‖²`. -/
theorem quartic_quad_le (x k : EuclSpace d) :
    2 * ‖x‖ ^ 2 * ‖k‖ ^ 2 + 4 * inner ℝ x k ^ 2 ≤ 6 * ‖x‖ ^ 2 * ‖k‖ ^ 2 := by
  have hcs : inner ℝ x k ^ 2 ≤ ‖x‖ ^ 2 * ‖k‖ ^ 2 := by
    have h1 : |inner ℝ x k| ^ 2 ≤ (‖x‖ * ‖k‖) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm x k) 2
    rw [sq_abs, mul_pow] at h1
    exact h1
  linarith

/-- **A superjet of the quartic `‖· - c‖⁴`.** -/
theorem superJet_quartic (c x : EuclSpace d) :
    ((4 * ‖x - c‖ ^ 2) • (x - c), (12 * ‖x - c‖ ^ 2) • idForm d)
      ∈ SuperJet (fun y => ‖y - c‖ ^ 4) x := by
  intro η hη
  have hT : Tendsto (fun y : EuclSpace d => y - x) (𝓝 x) (𝓝 0) := by
    have h0 : Continuous (fun y : EuclSpace d => y - x) := by fun_prop
    have := h0.tendsto x
    simpa using this
  filter_upwards [hT.eventually (eventually_penR_le (by norm_num : (0:ℝ) < 1 / 4)
    (x - c) hη)] with y hy
  change ‖y - c‖ ^ 4 ≤ ‖x - c‖ ^ 4 + inner ℝ ((4 * ‖x - c‖ ^ 2) • (x - c)) (y - x)
    + (1 / 2) * (((12 * ‖x - c‖ ^ 2) • idForm d) (y - x)) (y - x)
    + η * ‖y - x‖ ^ 2
  rw [smul_form_apply, idForm_apply]
  have e : y - c = (x - c) + (y - x) := by abel
  rw [e, quartic_expand]
  have hq := quartic_quad_le (x - c) (y - x)
  linarith

/-- **A subjet of the negated quartic.** -/
theorem subJet_neg_quartic (c x : EuclSpace d) :
    (-((4 * ‖x - c‖ ^ 2) • (x - c)), -((12 * ‖x - c‖ ^ 2) • idForm d))
      ∈ SubJet (fun y => -‖y - c‖ ^ 4) x :=
  subJet_neg_of_superJet (superJet_quartic c x)

/-- The gradient of the quartic tends to zero at its centre. -/
theorem tendsto_quartic_grad {c : EuclSpace d} {xs : ℕ → EuclSpace d}
    (hxs : Tendsto xs atTop (𝓝 c)) :
    Tendsto (fun n => (4 * ‖xs n - c‖ ^ 2) • (xs n - c)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n => xs n - c) atTop (𝓝 0) := by
    have := hxs.sub_const c
    simpa using this
  have h1 : Tendsto (fun n => 4 * ‖xs n - c‖ ^ 2) atTop (𝓝 (4 * ‖(0:EuclSpace d)‖ ^ 2)) :=
    (h0.norm.pow 2).const_mul 4
  have := h1.smul h0
  simpa using this

/-- The coefficient of the quartic's form tends to zero at its centre. -/
theorem tendsto_quartic_coef {c : EuclSpace d} {xs : ℕ → EuclSpace d}
    (hxs : Tendsto xs atTop (𝓝 c)) :
    Tendsto (fun n => 12 * ‖xs n - c‖ ^ 2) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n => xs n - c) atTop (𝓝 0) := by
    have := hxs.sub_const c
    simpa using this
  have := (h0.norm.pow 2).const_mul 12
  simpa using this

end

end PLaplacian
