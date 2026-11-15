/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.CoreLines

@[expose] public section

/-! # The concrete penalty

The reduction from the theorem of sums to its core produces the penalty

  `P(k) = s · S(k) + r ‖k‖²`,  `S = penQ α ĥ`,  `s, r ≥ 0`,

the Taylor bound giving `½ S + η ‖·‖²` and the decoupling a factor `1 + ε`.
This file supplies what the core consumes from it.

* **The upper Taylor bound** of `CoreLines`, which is here an exact expansion
  `P(d + k) = P(d) + ⟪g_d, k⟫ + P(k)` with `P(k) ≤ M ‖k‖²`, and the gradient
  bound `‖g_d‖ ≤ 2M ‖d‖`, which makes the gradients at the Jensen points tend
  to zero.

* **Young's inequality**, for the decoupling.

* **Convexity** of `(μ/2)(‖ξ‖² + ‖ζ‖²) - P(ξ - ζ)` for `μ ≥ 4M`, for the
  semiconvexity hypothesis of Jensen's lemma. Each quadratic piece satisfies
  `a Q(x) + b Q(y) - Q(a x + b y) = a b Q(x - y)` when `a + b = 1`, so the
  function's convexity defect is `a b` times its value at a difference, which
  is nonnegative.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- **The penalty.** -/
def penP (s r α : ℝ) (h0 k : EuclSpace d) : ℝ :=
  s * penQ α h0 k + r * ‖k‖ ^ 2

/-- **Its gradient** at `d`. -/
def penG (s r α : ℝ) (h0 dd : EuclSpace d) : EuclSpace d :=
  (2 * s * α⁻¹) • ((‖h0‖ ^ 2) • dd + (2 * inner ℝ h0 dd) • h0) + (2 * r) • dd

/-- The constant of the quadratic bound. -/
def penM (s r α : ℝ) (h0 : EuclSpace d) : ℝ := s * (3 * α⁻¹ * ‖h0‖ ^ 2) + r

section props

variable {s r α : ℝ} {h0 : EuclSpace d}

theorem inner_penG (dd k : EuclSpace d) :
    inner ℝ (penG s r α h0 dd) k
      = 2 * s * penB α h0 dd k + 2 * r * inner ℝ dd k := by
  unfold penG penB
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_add_left,
    real_inner_smul_left, real_inner_smul_left]
  ring

/-- **The exact expansion.** -/
theorem penP_add (dd k : EuclSpace d) :
    penP s r α h0 (dd + k)
      = penP s r α h0 dd + inner ℝ (penG s r α h0 dd) k + penP s r α h0 k := by
  unfold penP
  rw [penQ_add, inner_penG, norm_add_sq_real]
  ring

theorem penP_nonneg (hs : 0 ≤ s) (hr : 0 ≤ r) (hα : 0 < α) (k : EuclSpace d) :
    0 ≤ penP s r α h0 k := by
  unfold penP
  have := penQ_nonneg hα h0 k
  positivity

theorem penP_le (hs : 0 ≤ s) (hα : 0 < α) (k : EuclSpace d) :
    penP s r α h0 k ≤ penM s r α h0 * ‖k‖ ^ 2 := by
  unfold penP penM
  have := mul_le_mul_of_nonneg_left (penQ_le hα h0 k) hs
  nlinarith

/-- **The upper Taylor bound**, in the form `CoreLines` consumes. -/
theorem penP_taylor (hs : 0 ≤ s) (hα : 0 < α) (dd k : EuclSpace d) :
    penP s r α h0 (dd + k)
      ≤ penP s r α h0 dd + inner ℝ (penG s r α h0 dd) k
        + penM s r α h0 * ‖k‖ ^ 2 := by
  rw [penP_add]
  linarith [penP_le (r := r) (h0 := h0) hs hα k]

theorem penM_nonneg (hs : 0 ≤ s) (hr : 0 ≤ r) (hα : 0 < α) :
    0 ≤ penM s r α h0 := by
  unfold penM
  have : 0 ≤ α⁻¹ := inv_nonneg.2 hα.le
  positivity

/-- **The gradient bound**: `‖g_d‖ ≤ 2M ‖d‖`. -/
theorem norm_penG_le (hs : 0 ≤ s) (hr : 0 ≤ r) (hα : 0 < α) (dd : EuclSpace d) :
    ‖penG s r α h0 dd‖ ≤ 2 * penM s r α h0 * ‖dd‖ := by
  unfold penG penM
  have hinv : 0 ≤ α⁻¹ := inv_nonneg.2 hα.le
  have hin : |inner ℝ h0 dd| ≤ ‖h0‖ * ‖dd‖ := abs_real_inner_le_norm h0 dd
  have h1 : ‖(‖h0‖ ^ 2) • dd + (2 * inner ℝ h0 dd) • h0‖
      ≤ 3 * ‖h0‖ ^ 2 * ‖dd‖ := by
    calc ‖(‖h0‖ ^ 2) • dd + (2 * inner ℝ h0 dd) • h0‖
        ≤ ‖(‖h0‖ ^ 2) • dd‖ + ‖(2 * inner ℝ h0 dd) • h0‖ := norm_add_le _ _
      _ = ‖h0‖ ^ 2 * ‖dd‖ + 2 * |inner ℝ h0 dd| * ‖h0‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (sq_nonneg _), abs_mul, abs_two]
      _ ≤ ‖h0‖ ^ 2 * ‖dd‖ + 2 * (‖h0‖ * ‖dd‖) * ‖h0‖ := by
          have := mul_le_mul_of_nonneg_right hin (norm_nonneg h0)
          nlinarith
      _ = 3 * ‖h0‖ ^ 2 * ‖dd‖ := by ring
  calc ‖(2 * s * α⁻¹) • ((‖h0‖ ^ 2) • dd + (2 * inner ℝ h0 dd) • h0)
        + (2 * r) • dd‖
      ≤ ‖(2 * s * α⁻¹) • ((‖h0‖ ^ 2) • dd + (2 * inner ℝ h0 dd) • h0)‖
        + ‖(2 * r) • dd‖ := norm_add_le _ _
    _ = (2 * s * α⁻¹) * ‖(‖h0‖ ^ 2) • dd + (2 * inner ℝ h0 dd) • h0‖
        + 2 * r * ‖dd‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    _ ≤ (2 * s * α⁻¹) * (3 * ‖h0‖ ^ 2 * ‖dd‖) + 2 * r * ‖dd‖ := by
        have : 0 ≤ 2 * s * α⁻¹ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h1 this]
    _ = 2 * (s * (3 * α⁻¹ * ‖h0‖ ^ 2) + r) * ‖dd‖ := by ring

/-- **Young's inequality for the penalty.** -/
theorem penP_young (hs : 0 ≤ s) (hr : 0 ≤ r) (hα : 0 < α) {ε : ℝ} (hε : 0 < ε)
    (a b : EuclSpace d) :
    penP s r α h0 (a + b)
      ≤ (1 + ε) * penP s r α h0 a + (1 + 1 / ε) * penP s r α h0 b := by
  unfold penP
  have h1 := mul_le_mul_of_nonneg_left (penQ_young (h0 := h0) hα hε a b) hs
  have hn : ‖a + b‖ ^ 2 ≤ (1 + ε) * ‖a‖ ^ 2 + (1 + 1 / ε) * ‖b‖ ^ 2 := by
    rw [norm_add_sq_real]
    have := young_inner hε a b
    have e : ‖b‖ ^ 2 / ε = 1 / ε * ‖b‖ ^ 2 := by ring
    rw [e] at this
    linarith
  have h2 := mul_le_mul_of_nonneg_left hn hr
  nlinarith

end props

/-! ## Convexity -/

/-- The convexity defect of the squared norm. -/
theorem norm_sq_convex_comb {a b : ℝ} (hab : a + b = 1) (x y : EuclSpace d) :
    ‖a • x + b • y‖ ^ 2 = a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 - a * b * ‖x - y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul,
    real_inner_smul_left, real_inner_smul_right, Real.norm_eq_abs,
    Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
  have hb : b = 1 - a := by linarith
  subst hb
  ring

/-- The convexity defect of the quadratic form `S`. -/
theorem penQ_convex_comb {α a b : ℝ} (hab : a + b = 1) (h0 x y : EuclSpace d) :
    penQ α h0 (a • x + b • y)
      = a * penQ α h0 x + b * penQ α h0 y - a * b * penQ α h0 (x - y) := by
  unfold penQ
  rw [norm_sq_convex_comb hab, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, inner_sub_right]
  have hb : b = 1 - a := by linarith
  subst hb
  ring

/-- The convexity defect of the penalty. -/
theorem penP_convex_comb {s r α a b : ℝ} (hab : a + b = 1) (h0 x y : EuclSpace d) :
    penP s r α h0 (a • x + b • y)
      = a * penP s r α h0 x + b * penP s r α h0 y
        - a * b * penP s r α h0 (x - y) := by
  unfold penP
  rw [penQ_convex_comb hab, norm_sq_convex_comb hab]
  ring

/-- **The quadratic part of the doubled function is convex** for `μ ≥ 4M`. -/
theorem convexOn_quadPart {s r α μ : ℝ} {h0 : EuclSpace d} (hs : 0 ≤ s)
    (hr : 0 ≤ r) (hα : 0 < α) (hμ : 4 * penM s r α h0 ≤ μ) :
    ConvexOn ℝ univ (fun z : EuclSpace d × EuclSpace d =>
      μ / 2 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2) - penP s r α h0 (z.1 - z.2)) := by
  refine ⟨convex_univ, fun z₁ _ z₂ _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
  have e4 : a • z₁.1 + b • z₂.1 - (a • z₁.2 + b • z₂.2)
      = a • (z₁.1 - z₁.2) + b • (z₂.1 - z₂.2) := by
    rw [smul_sub, smul_sub]; abel
  rw [e4, norm_sq_convex_comb hab z₁.1 z₂.1, norm_sq_convex_comb hab z₁.2 z₂.2,
    penP_convex_comb hab]
  -- the defect is a b times the function at the difference, which is ≥ 0
  have e5 : z₁.1 - z₁.2 - (z₂.1 - z₂.2) = (z₁.1 - z₂.1) - (z₁.2 - z₂.2) := by abel
  rw [e5]
  have hpen := penP_le (r := r) (h0 := h0) hs hα ((z₁.1 - z₂.1) - (z₁.2 - z₂.2))
  have hsq : ‖(z₁.1 - z₂.1) - (z₁.2 - z₂.2)‖ ^ 2
      ≤ 2 * (‖z₁.1 - z₂.1‖ ^ 2 + ‖z₁.2 - z₂.2‖ ^ 2) := by
    rw [norm_sub_sq_real]
    have := young_inner (one_pos) (z₁.1 - z₂.1) (-(z₁.2 - z₂.2))
    rw [inner_neg_right, norm_neg] at this
    linarith
  have hM : 0 ≤ penM s r α h0 := penM_nonneg hs hr hα
  have hF : 0 ≤ μ / 2 * (‖z₁.1 - z₂.1‖ ^ 2 + ‖z₁.2 - z₂.2‖ ^ 2)
      - penP s r α h0 ((z₁.1 - z₂.1) - (z₁.2 - z₂.2)) := by
    have h1 := mul_le_mul_of_nonneg_left hsq hM
    nlinarith
  have hab0 : 0 ≤ a * b := mul_nonneg ha hb
  nlinarith [mul_nonneg hab0 hF]

end

end PLaplacian
