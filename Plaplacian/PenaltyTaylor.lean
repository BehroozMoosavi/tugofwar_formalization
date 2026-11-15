/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.JetAlgebra

@[expose] public section

/-! # The penalty, expanded

The quartic penalty `g(h) = ‖h‖⁴ / (4α)` is a polynomial, and it expands
exactly about any point `ĥ`. With `N = ‖ĥ‖²`, squaring
`‖ĥ + k‖² = N + 2⟪ĥ, k⟫ + ‖k‖²` gives

  `g(ĥ + k) = g(ĥ) + ⟪q, k⟫ + ½ S(k) + R(k)`,

  `q = (N/α) ĥ`,  `S(k) = (N ‖k‖² + 2⟪ĥ, k⟫²)/α`,
  `R(k) = (⟪ĥ, k⟫ ‖k‖² + ‖k‖⁴/4)/α`.

The gradient `q` is the penalty gradient of the theorem of sums; the quadratic
form `S` is written out explicitly and is symmetric, which avoids the curried
Hessian entirely; and `R` is cubic, hence below `η ‖k‖²` near zero. No
derivative is computed.

Also proved here is what the decoupling consumes: `S` is nonnegative, bounded
by a multiple of `‖k‖²`, and satisfies Young's inequality
`S(a + b) ≤ (1 + ε) S(a) + (1 + 1/ε) S(b)`.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- The bilinear form of the second-order term. -/
def penB (α : ℝ) (h0 a b : EuclSpace d) : ℝ :=
  α⁻¹ * (‖h0‖ ^ 2 * inner ℝ a b + 2 * (inner ℝ h0 a * inner ℝ h0 b))

/-- **The quadratic form of the second-order term.** -/
def penQ (α : ℝ) (h0 k : EuclSpace d) : ℝ :=
  α⁻¹ * (‖h0‖ ^ 2 * ‖k‖ ^ 2 + 2 * inner ℝ h0 k ^ 2)

/-- The cubic remainder. -/
def penR (α : ℝ) (h0 k : EuclSpace d) : ℝ :=
  α⁻¹ * (inner ℝ h0 k * ‖k‖ ^ 2 + ‖k‖ ^ 4 / 4)

theorem penQ_eq_penB (α : ℝ) (h0 k : EuclSpace d) :
    penQ α h0 k = penB α h0 k k := by
  unfold penQ penB
  rw [real_inner_self_eq_norm_sq]; ring

/-- **The exact expansion of the penalty.** -/
theorem penalty_expand {α : ℝ} (hα : 0 < α) (h0 k : EuclSpace d) :
    ‖h0 + k‖ ^ 4 / (4 * α)
      = ‖h0‖ ^ 4 / (4 * α) + inner ℝ ((‖h0‖ ^ 2 / α) • h0) k
        + (1 / 2) * penQ α h0 k + penR α h0 k := by
  have hne : α ≠ 0 := hα.ne'
  have hsq : ‖h0 + k‖ ^ 4 = (‖h0 + k‖ ^ 2) ^ 2 := by ring
  rw [hsq, norm_add_sq_real, real_inner_smul_left]
  unfold penQ penR
  field_simp
  ring

/-- **The remainder is below any multiple of the square, near zero.** -/
theorem eventually_penR_le {α : ℝ} (hα : 0 < α) (h0 : EuclSpace d) {η : ℝ}
    (hη : 0 < η) : ∀ᶠ k in 𝓝 (0 : EuclSpace d), penR α h0 k ≤ η * ‖k‖ ^ 2 := by
  have hc : (0:ℝ) < ‖h0‖ + 1 := by positivity
  have hδ : (0:ℝ) < min 1 (η * α / (‖h0‖ + 1)) := lt_min one_pos (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : EuclSpace d) hδ] with k hk
  rw [mem_ball, dist_zero_right] at hk
  set r := ‖k‖ with hrdef
  have hr0 : 0 ≤ r := norm_nonneg k
  have hr1 : r < 1 := lt_of_lt_of_le hk (min_le_left _ _)
  have hr2 : r < η * α / (‖h0‖ + 1) := lt_of_lt_of_le hk (min_le_right _ _)
  have hin : inner ℝ h0 k ≤ ‖h0‖ * r := real_inner_le_norm h0 k
  have e1 : inner ℝ h0 k * r ^ 2 ≤ ‖h0‖ * r ^ 3 := by
    calc inner ℝ h0 k * r ^ 2 ≤ (‖h0‖ * r) * r ^ 2 :=
          mul_le_mul_of_nonneg_right hin (sq_nonneg r)
      _ = ‖h0‖ * r ^ 3 := by ring
  have hr3 : 0 ≤ r ^ 3 := pow_nonneg hr0 3
  have e2 : r ^ 4 ≤ r ^ 3 := by
    have : r ^ 4 = r ^ 3 * r := by ring
    rw [this]
    calc r ^ 3 * r ≤ r ^ 3 * 1 := mul_le_mul_of_nonneg_left hr1.le hr3
      _ = r ^ 3 := mul_one _
  have e4 : r * (‖h0‖ + 1) ≤ η * α := ((lt_div_iff₀ hc).1 hr2).le
  have hnorm0 : (0:ℝ) ≤ ‖h0‖ := norm_nonneg h0
  have e5 : inner ℝ h0 k * r ^ 2 + r ^ 4 / 4 ≤ r ^ 2 * (η * α) := by
    have e3 : ‖h0‖ * r ^ 3 + r ^ 3 / 4 ≤ r ^ 2 * (r * (‖h0‖ + 1)) := by
      nlinarith
    have e6 : r ^ 2 * (r * (‖h0‖ + 1)) ≤ r ^ 2 * (η * α) :=
      mul_le_mul_of_nonneg_left e4 (sq_nonneg r)
    linarith
  unfold penR
  calc α⁻¹ * (inner ℝ h0 k * r ^ 2 + r ^ 4 / 4)
      ≤ α⁻¹ * (r ^ 2 * (η * α)) :=
        mul_le_mul_of_nonneg_left e5 (inv_nonneg.2 hα.le)
    _ = η * r ^ 2 := by field_simp

/-- **The Taylor bound of the penalty**: near `ĥ`, the penalty lies below its
second-order polynomial plus `η ‖k‖²`. -/
theorem penalty_upper {α : ℝ} (hα : 0 < α) (h0 : EuclSpace d) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ k in 𝓝 (0 : EuclSpace d),
      ‖h0 + k‖ ^ 4 / (4 * α)
        ≤ ‖h0‖ ^ 4 / (4 * α) + inner ℝ ((‖h0‖ ^ 2 / α) • h0) k
          + (1 / 2) * penQ α h0 k + η * ‖k‖ ^ 2 := by
  filter_upwards [eventually_penR_le hα h0 hη] with k hk
  rw [penalty_expand hα h0 k]
  linarith

/-- The penalty gradient is the gradient of the expansion. -/
theorem penaltyGrad_eq (α : ℝ) (x y : EuclSpace d) :
    penaltyGrad α x y = (‖x - y‖ ^ 2 / α) • (x - y) := rfl

/-! ## The quadratic form, for the decoupling -/

theorem penQ_nonneg {α : ℝ} (hα : 0 < α) (h0 k : EuclSpace d) :
    0 ≤ penQ α h0 k := by
  unfold penQ; positivity

/-- The quadratic form is bounded by a multiple of the square. -/
theorem penQ_le {α : ℝ} (hα : 0 < α) (h0 k : EuclSpace d) :
    penQ α h0 k ≤ 3 * α⁻¹ * ‖h0‖ ^ 2 * ‖k‖ ^ 2 := by
  unfold penQ
  have hcs : inner ℝ h0 k ^ 2 ≤ ‖h0‖ ^ 2 * ‖k‖ ^ 2 := by
    have := abs_real_inner_le_norm h0 k
    have h1 : |inner ℝ h0 k| ^ 2 ≤ (‖h0‖ * ‖k‖) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) this 2
    rw [sq_abs, mul_pow] at h1
    exact h1
  have hinv : 0 ≤ α⁻¹ := inv_nonneg.2 hα.le
  calc α⁻¹ * (‖h0‖ ^ 2 * ‖k‖ ^ 2 + 2 * inner ℝ h0 k ^ 2)
      ≤ α⁻¹ * (‖h0‖ ^ 2 * ‖k‖ ^ 2 + 2 * (‖h0‖ ^ 2 * ‖k‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) hinv
    _ = 3 * α⁻¹ * ‖h0‖ ^ 2 * ‖k‖ ^ 2 := by ring

/-- The quadratic form of a sum. -/
theorem penQ_add (α : ℝ) (h0 a b : EuclSpace d) :
    penQ α h0 (a + b) = penQ α h0 a + 2 * penB α h0 a b + penQ α h0 b := by
  unfold penQ penB
  rw [norm_add_sq_real, inner_add_right]
  ring

/-- Young's inequality for reals. -/
theorem young_real {ε : ℝ} (hε : 0 < ε) (x y : ℝ) :
    2 * x * y ≤ ε * x ^ 2 + y ^ 2 / ε := by
  have h1 : ε * (y ^ 2 / ε) = y ^ 2 := by field_simp
  have h : ε * (2 * x * y) ≤ ε * (ε * x ^ 2 + y ^ 2 / ε) := by
    nlinarith [sq_nonneg (ε * x - y)]
  exact le_of_mul_le_mul_left h hε

/-- Young's inequality for the inner product. -/
theorem young_inner {ε : ℝ} (hε : 0 < ε) (a b : EuclSpace d) :
    2 * inner ℝ a b ≤ ε * ‖a‖ ^ 2 + ‖b‖ ^ 2 / ε := by
  have hsq := norm_sub_sq_real (ε • a) b
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left] at hsq
  have h0 : 0 ≤ ‖ε • a - b‖ ^ 2 := sq_nonneg _
  have h1 : ε * (‖b‖ ^ 2 / ε) = ‖b‖ ^ 2 := by field_simp
  have h : ε * (2 * inner ℝ a b) ≤ ε * (ε * ‖a‖ ^ 2 + ‖b‖ ^ 2 / ε) := by
    nlinarith
  exact le_of_mul_le_mul_left h hε

/-- Young's inequality for the bilinear form. -/
theorem penB_young {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) (h0 a b : EuclSpace d) :
    2 * penB α h0 a b ≤ ε * penQ α h0 a + penQ α h0 b / ε := by
  have h1 := young_inner hε a b
  have h2 := young_real hε (inner ℝ h0 a) (inner ℝ h0 b)
  have hN : 0 ≤ ‖h0‖ ^ 2 := sq_nonneg _
  have hN1 := mul_le_mul_of_nonneg_left h1 hN
  have key : ‖h0‖ ^ 2 * (2 * inner ℝ a b) + 2 * (2 * (inner ℝ h0 a * inner ℝ h0 b))
      ≤ ‖h0‖ ^ 2 * (ε * ‖a‖ ^ 2 + ‖b‖ ^ 2 / ε)
        + 2 * (ε * inner ℝ h0 a ^ 2 + inner ℝ h0 b ^ 2 / ε) := by
    nlinarith
  have hinv : 0 ≤ α⁻¹ := inv_nonneg.2 hα.le
  have hmul := mul_le_mul_of_nonneg_left key hinv
  unfold penB penQ
  have eL : 2 * (α⁻¹ * (‖h0‖ ^ 2 * inner ℝ a b + 2 * (inner ℝ h0 a * inner ℝ h0 b)))
      = α⁻¹ * (‖h0‖ ^ 2 * (2 * inner ℝ a b)
          + 2 * (2 * (inner ℝ h0 a * inner ℝ h0 b))) := by ring
  have eR : ε * (α⁻¹ * (‖h0‖ ^ 2 * ‖a‖ ^ 2 + 2 * inner ℝ h0 a ^ 2))
        + α⁻¹ * (‖h0‖ ^ 2 * ‖b‖ ^ 2 + 2 * inner ℝ h0 b ^ 2) / ε
      = α⁻¹ * (‖h0‖ ^ 2 * (ε * ‖a‖ ^ 2 + ‖b‖ ^ 2 / ε)
          + 2 * (ε * inner ℝ h0 a ^ 2 + inner ℝ h0 b ^ 2 / ε)) := by ring
  rw [eL, eR]
  exact hmul

/-- **Young's inequality for the quadratic form**, the decoupling estimate. -/
theorem penQ_young {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) (h0 a b : EuclSpace d) :
    penQ α h0 (a + b) ≤ (1 + ε) * penQ α h0 a + (1 + 1 / ε) * penQ α h0 b := by
  rw [penQ_add]
  have h := penB_young hα hε h0 a b
  have e : penQ α h0 b / ε = 1 / ε * penQ α h0 b := by ring
  rw [e] at h
  linarith

end

end PLaplacian
