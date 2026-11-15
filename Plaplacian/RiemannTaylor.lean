/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.SubgradApprox

@[expose] public section

/-! # The second-order expansion, by Riemann sums

Suppose a selection `z ↦ p_z` of subgradients of `f` is approximated, near `x`,
by `p_z ≈ p₀ + A(z - x)`. Then

  `f(x + h) = f(x) + ⟪p₀, h⟫ + ½ ⟪A h, h⟫ + o(‖h‖²)`.

No integral is used. Splitting `[x, x + h]` into `N` steps `z_k = x + (k/N) h`,
the subgradient inequalities at the two ends of a step give

  `(1/N) ⟪p_{z_k}, h⟫ ≤ f(z_{k+1}) - f(z_k) ≤ (1/N) ⟪p_{z_{k+1}}, h⟫`,

and with `⟪p_{z_k}, h⟫ = ⟪p₀, h⟫ + (k/N) Q + O(ε ‖h‖²)`, `Q = ⟪A h, h⟫`, the sums
telescope, `∑_{k<N} k = N(N-1)/2`, to

  `|f(x + h) - f(x) - ⟪p₀, h⟫ - ½ Q| ≤ |Q|/(2N) + (ε/2) ‖h‖²`.

Choosing `N ≥ ‖A‖/ε` makes this at most `ε ‖h‖²`: a Riemann sum for
`∫₀¹ t dt = ½`, with its error controlled.
-/

open Set Topology Filter MeasureTheory Metric Finset

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- The sum of an affine function over a range. -/
theorem sum_range_affine (N : ℕ) (a b : ℝ) :
    ∑ k ∈ range N, (a + b * (k : ℝ)) = N * a + b * ((N : ℝ) * ((N : ℝ) - 1) / 2) := by
  induction N with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; push_cast; ring

/-- **The second-order expansion from a linear approximation of subgradients.** -/
theorem peano_of_approx {f : EuclSpace d → ℝ} {x p0 : EuclSpace d}
    {A : EuclSpace d →L[ℝ] EuclSpace d} {sel : EuclSpace d → EuclSpace d}
    (hsel : ∀ z, IsSubgrad f z (sel z))
    (happrox : ∀ ε > 0, ∃ δ > 0, ∀ z, ‖z - x‖ < δ →
      ‖sel z - p0 - A (z - x)‖ ≤ ε * ‖z - x‖)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ h : EuclSpace d, ‖h‖ < δ →
      |f (x + h) - f x - inner ℝ p0 h - 1 / 2 * inner ℝ (A h) h| ≤ ε * ‖h‖ ^ 2 := by
  set CA := ‖A‖ with hCA
  have hCA0 : 0 ≤ CA := norm_nonneg _
  -- the number of steps
  set N : ℕ := ⌈CA / ε⌉₊ + 1 with hNdef
  set Nr : ℝ := (N : ℝ) with hNr
  have hN1 : (1 : ℝ) ≤ Nr := by
    rw [hNr, hNdef]; push_cast; have := Nat.cast_nonneg (α := ℝ) ⌈CA / ε⌉₊; linarith
  have hNpos : 0 < Nr := by linarith
  have hCAN : CA ≤ ε * Nr := by
    have h1 : CA / ε ≤ (⌈CA / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : CA / ε ≤ Nr := by rw [hNr, hNdef]; push_cast; linarith
    rw [div_le_iff₀ hε] at h2
    linarith
  obtain ⟨δ, hδ, hap⟩ := happrox (ε / 2) (by positivity)
  refine ⟨δ, hδ, fun h hh => ?_⟩
  set z : ℕ → EuclSpace d := fun k => x + ((k : ℝ) / Nr) • h with hzdef
  set Q := inner ℝ (A h) h with hQ
  set c := inner ℝ p0 h with hc
  set e := ε / 2 * ‖h‖ ^ 2 with he
  have hz0 : z 0 = x := by simp [hzdef]
  have hzN : z N = x + h := by
    simp only [hzdef]
    rw [show ((N : ℝ) / Nr) = 1 by rw [hNr]; exact div_self hNpos.ne', one_smul]
  have hdz : ∀ k, z (k + 1) - z k = (1 / Nr) • h := by
    intro k
    simp only [hzdef]
    rw [show x + (((k + 1 : ℕ) : ℝ) / Nr) • h - (x + ((k : ℝ) / Nr) • h)
        = ((((k + 1 : ℕ) : ℝ) / Nr) - (k : ℝ) / Nr) • h by rw [sub_smul]; abel]
    congr 1
    push_cast
    field_simp
    ring
  have hzx : ∀ k, k ≤ N → ‖z k - x‖ ≤ ‖h‖ := by
    intro k hk
    have e1 : z k - x = ((k : ℝ) / Nr) • h := by simp [hzdef]
    rw [e1, norm_smul, Real.norm_eq_abs]
    have hk0 : 0 ≤ (k : ℝ) / Nr := by positivity
    have hk1 : (k : ℝ) / Nr ≤ 1 := by
      rw [div_le_one hNpos, hNr]; exact_mod_cast hk
    rw [abs_of_nonneg hk0]
    calc (k : ℝ) / Nr * ‖h‖ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right hk1 (norm_nonneg h)
      _ = ‖h‖ := one_mul _
  -- the subgradients along the segment
  have hak : ∀ k, k ≤ N → |inner ℝ (sel (z k)) h - (c + (k : ℝ) / Nr * Q)| ≤ e := by
    intro k hk
    have hzk := hzx k hk
    have hb := hap (z k) (lt_of_le_of_lt hzk hh)
    have e1 : z k - x = ((k : ℝ) / Nr) • h := by simp [hzdef]
    have e2 : inner ℝ (sel (z k)) h - (c + (k : ℝ) / Nr * Q)
        = inner ℝ (sel (z k) - p0 - A (z k - x)) h := by
      rw [e1, map_smul, inner_sub_left, inner_sub_left, real_inner_smul_left]
      rw [hc, hQ]; ring
    rw [e2]
    calc |inner ℝ (sel (z k) - p0 - A (z k - x)) h|
        ≤ ‖sel (z k) - p0 - A (z k - x)‖ * ‖h‖ := abs_real_inner_le_norm _ _
      _ ≤ (ε / 2 * ‖z k - x‖) * ‖h‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg h)
      _ ≤ (ε / 2 * ‖h‖) * ‖h‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg h)
          exact mul_le_mul_of_nonneg_left hzk (by positivity)
      _ = e := by rw [he]; ring
  -- the increments along the segment
  have hlow : ∀ k, (1 / Nr) * inner ℝ (sel (z k)) h ≤ f (z (k + 1)) - f (z k) := by
    intro k
    have h1 := hsel (z k) (z (k + 1))
    rw [hdz k, real_inner_smul_right] at h1
    linarith
  have hupp : ∀ k, f (z (k + 1)) - f (z k) ≤ (1 / Nr) * inner ℝ (sel (z (k + 1))) h := by
    intro k
    have h1 := hsel (z (k + 1)) (z k)
    have e1 : z k - z (k + 1) = -((1 / Nr) • h) := by rw [← hdz k]; abel
    rw [e1, inner_neg_right, real_inner_smul_right] at h1
    linarith
  -- telescoping
  have hS : f (x + h) - f x = ∑ k ∈ range N, (f (z (k + 1)) - f (z k)) := by
    rw [sum_range_sub (fun k => f (z k)) N, hzN, hz0]
  -- the lower sum
  have hL : ∑ k ∈ range N, ((1 / Nr) * (c - e) + Q / Nr ^ 2 * (k : ℝ)) ≤ f (x + h) - f x := by
    rw [hS]
    apply sum_le_sum
    intro k hk
    have hk' : k ≤ N := (mem_range.1 hk).le
    have h1 := (abs_le.1 (hak k hk')).1
    have h2 := hlow k
    have e3 : (1 / Nr) * (c - e) + Q / Nr ^ 2 * (k : ℝ)
        = (1 / Nr) * (c + (k : ℝ) / Nr * Q - e) := by field_simp; ring
    rw [e3]
    have h3 := mul_le_mul_of_nonneg_left
      (by linarith : c + (k : ℝ) / Nr * Q - e ≤ inner ℝ (sel (z k)) h)
      (by positivity : (0 : ℝ) ≤ 1 / Nr)
    linarith
  have hLval : ∑ k ∈ range N, ((1 / Nr) * (c - e) + Q / Nr ^ 2 * (k : ℝ))
      = (c - e) + Q * (Nr - 1) / (2 * Nr) := by
    rw [sum_range_affine]
    rw [← hNr]
    field_simp
  -- the upper sum
  have hU : f (x + h) - f x
      ≤ ∑ k ∈ range N, ((1 / Nr) * (c + Q / Nr + e) + Q / Nr ^ 2 * (k : ℝ)) := by
    rw [hS]
    apply sum_le_sum
    intro k hk
    have hk' : k + 1 ≤ N := mem_range.1 hk
    have h1 := (abs_le.1 (hak (k + 1) hk')).2
    have h2 := hupp k
    have e3 : (1 / Nr) * (c + Q / Nr + e) + Q / Nr ^ 2 * (k : ℝ)
        = (1 / Nr) * (c + ((k + 1 : ℕ) : ℝ) / Nr * Q + e) := by push_cast; field_simp; ring
    rw [e3]
    have h3 := mul_le_mul_of_nonneg_left
      (by linarith : inner ℝ (sel (z (k + 1))) h ≤ c + ((k + 1 : ℕ) : ℝ) / Nr * Q + e)
      (by positivity : (0 : ℝ) ≤ 1 / Nr)
    linarith
  have hUval : ∑ k ∈ range N, ((1 / Nr) * (c + Q / Nr + e) + Q / Nr ^ 2 * (k : ℝ))
      = (c + e) + Q * (Nr + 1) / (2 * Nr) := by
    rw [sum_range_affine]
    rw [← hNr]
    field_simp
    ring
  rw [hLval] at hL
  rw [hUval] at hU
  -- the quadratic term
  have hQb : |Q| ≤ CA * ‖h‖ ^ 2 := by
    calc |Q| ≤ ‖A h‖ * ‖h‖ := abs_real_inner_le_norm _ _
      _ ≤ (CA * ‖h‖) * ‖h‖ := mul_le_mul_of_nonneg_right (A.le_opNorm h) (norm_nonneg h)
      _ = CA * ‖h‖ ^ 2 := by ring
  have hQN : |Q| / (2 * Nr) ≤ ε / 2 * ‖h‖ ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : CA * ‖h‖ ^ 2 ≤ ε * Nr * ‖h‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hCAN (by positivity)
    nlinarith
  have hlow2 : -(e + |Q| / (2 * Nr)) ≤ f (x + h) - f x - c - 1 / 2 * Q := by
    have e1 : (c - e) + Q * (Nr - 1) / (2 * Nr) = c + 1 / 2 * Q - e - Q / (2 * Nr) := by
      field_simp; ring
    have : Q / (2 * Nr) ≤ |Q| / (2 * Nr) :=
      div_le_div_of_nonneg_right (le_abs_self Q) (by positivity)
    linarith
  have hupp2 : f (x + h) - f x - c - 1 / 2 * Q ≤ e + |Q| / (2 * Nr) := by
    have e1 : (c + e) + Q * (Nr + 1) / (2 * Nr) = c + 1 / 2 * Q + e + Q / (2 * Nr) := by
      field_simp; ring
    have : Q / (2 * Nr) ≤ |Q| / (2 * Nr) :=
      div_le_div_of_nonneg_right (le_abs_self Q) (by positivity)
    linarith
  rw [abs_le]
  constructor <;> nlinarith

end

end PLaplacian
