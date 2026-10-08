/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.SMPMin

/-! # The change of values, at the level of jets

With `ψ(s) = s - η s²`, a supersolution `V` becomes `W = ψ(V)`, which is strict
away from critical points: at a point where `V` has the expansion `(q, X)`,
`W` has the expansion `(c q, c X - 2η q ⊗ q)`, `c = 1 - 2η V(x)`, and

  `Δᴺₚ(c q, c X + b q ⊗ q) = c Δᴺₚ(q, X) + (p - 1) b ‖q‖²`,

so `Δᴺₚ(q, X) ≤ 0` gives `Δᴺₚ(c q, c X - 2η q ⊗ q) ≤ -2η(p - 1)‖q‖²`.

The comparison argument uses this at points where `V` is twice differentiable,
so only Peano expansions are composed: no viscosity chain rule is needed. The
error of the composed expansion is `c(a - L - Q) - η(a² - L²)`, with
`a = V(x + h) - V(x)`, `L = ⟪q, h⟫`, `Q = ½ X(h, h)`, and
`|a² - L²| = |a - L| |a + L| = O(‖h‖³)`.
-/

open Set Topology Filter Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-! ## The operator identity -/

/-- **The operator after a change of values**, for `a > 0` and `q ≠ 0`. -/
theorem normPLapOf_cv {p : ℝ} {q : EuclSpace d} (hq : q ≠ 0) {a b : ℝ} (ha : 0 < a)
    (X : Bilin d) :
    normPLapOf p (a • q) (a • X + b • rankOne q)
      = a * normPLapOf p q X + (p - 1) * b * ‖q‖ ^ 2 := by
  have hqn : 0 < ‖q‖ := norm_pos_iff.2 hq
  unfold normPLapOf infLaplacianOf
  rw [laplacianOf_add, laplacianOf_smul, laplacianOf_smul, laplacianOf_rankOne]
  have hn : ‖a • q‖ = a * ‖q‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  have he : ‖a • q‖⁻¹ • (a • q) = ‖q‖⁻¹ • q := by
    rw [hn, smul_smul]
    congr 1
    field_simp
  rw [he]
  have h2 : inner ℝ q (‖q‖⁻¹ • q) = ‖q‖ := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  rw [add_apply, add_apply, smul_apply, smul_apply, smul_apply, smul_apply, smul_eq_mul,
    smul_eq_mul, rankOne_apply, h2]
  ring

/-- **The operator after a change of values**, subtraction form. -/
theorem normPLapOf_cv_sub {p : ℝ} {q : EuclSpace d} (hq : q ≠ 0) {a b : ℝ} (ha : 0 < a)
    (X : Bilin d) :
    normPLapOf p (a • q) (a • X - b • rankOne q)
      = a * normPLapOf p q X - (p - 1) * b * ‖q‖ ^ 2 := by
  have hqn : 0 < ‖q‖ := norm_pos_iff.2 hq
  unfold normPLapOf infLaplacianOf
  rw [laplacianOf_sub, laplacianOf_smul, laplacianOf_smul, laplacianOf_rankOne]
  have hn : ‖a • q‖ = a * ‖q‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  have he : ‖a • q‖⁻¹ • (a • q) = ‖q‖⁻¹ • q := by
    rw [hn, smul_smul]
    congr 1
    field_simp
  rw [he]
  have h2 : inner ℝ q (‖q‖⁻¹ • q) = ‖q‖ := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  rw [sub_apply, sub_apply, smul_apply, smul_apply, smul_apply, smul_apply, smul_eq_mul,
    smul_eq_mul, rankOne_apply, h2]
  ring

/-- **Strictness away from critical points.** -/
theorem normPLapOf_cv_strict {p : ℝ} (_hp : 2 ≤ p) {q : EuclSpace d} (hq : q ≠ 0)
    {c η : ℝ} (hc : 0 < c) (_hη : 0 ≤ η) {X : Bilin d} (hX : normPLapOf p q X ≤ 0) :
    normPLapOf p (c • q) (c • X - (2 * η) • rankOne q) ≤ -(2 * η * (p - 1) * ‖q‖ ^ 2) := by
  rw [normPLapOf_cv_sub hq hc]
  have : c * normPLapOf p q X ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le hX
  nlinarith

/-! ## Peano expansions -/

/-- **The Peano expansion**, in `ε`–`δ` form. -/
def PeanoAt (f : EuclSpace d → ℝ) (x q : EuclSpace d) (X : Bilin d) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ h : EuclSpace d, ‖h‖ < δ →
    |f (x + h) - f x - inner ℝ q h - 1 / 2 * (X h) h| ≤ ε * ‖h‖ ^ 2

theorem peanoAt_of_twiceDiffAt {f : EuclSpace d → ℝ} {x q : EuclSpace d} {X : Bilin d}
    (h : TwiceDiffAt f x q X) : PeanoAt f x q X := by
  obtain ⟨h1, h2⟩ := h
  have h1' : ∀ η > 0, ∀ᶠ y in 𝓝 x, f y ≤ f x + inner ℝ q (y - x)
      + 1 / 2 * (X (y - x)) (y - x) + η * ‖y - x‖ ^ 2 := h1
  have h2' : ∀ η > 0, ∀ᶠ y in 𝓝 x, f x + inner ℝ q (y - x)
      + 1 / 2 * (X (y - x)) (y - x) - η * ‖y - x‖ ^ 2 ≤ f y := h2
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 ((h1' ε hε).and (h2' ε hε))
  refine ⟨δ, hδ, fun k hk => ?_⟩
  have hk' : dist (x + k) x < δ := by
    rw [dist_eq_norm]
    have e : x + k - x = k := by abel
    rw [e]; exact hk
  obtain ⟨a1, a2⟩ := hb hk'
  have e : x + k - x = k := by abel
  rw [e] at a1 a2
  rw [abs_le]
  constructor <;> linarith

theorem twiceDiffAt_of_peanoAt {f : EuclSpace d → ℝ} {x q : EuclSpace d} {X : Bilin d}
    (h : PeanoAt f x q X) : TwiceDiffAt f x q X := by
  refine ⟨?_, ?_⟩
  · intro η hη
    obtain ⟨δ, hδ, hb⟩ := h η hη
    filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
    rw [mem_ball, dist_eq_norm] at hy
    have h1 := (abs_le.1 (hb (y - x) hy)).2
    have e : x + (y - x) = y := by abel
    rw [e] at h1
    change f y ≤ f x + inner ℝ q (y - x) + 1 / 2 * (X (y - x)) (y - x) + η * ‖y - x‖ ^ 2
    linarith
  · intro η hη
    obtain ⟨δ, hδ, hb⟩ := h η hη
    filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
    rw [mem_ball, dist_eq_norm] at hy
    have h1 := (abs_le.1 (hb (y - x) hy)).1
    have e : x + (y - x) = y := by abel
    rw [e] at h1
    change f x + inner ℝ q (y - x) + 1 / 2 * (X (y - x)) (y - x) - η * ‖y - x‖ ^ 2 ≤ f y
    linarith

/-! ## Composition with `ψ(s) = s - η s²` -/

/-- **The error estimate of the composed expansion**, in a small context. -/
theorem cv_arith {a L Q c η t ε K qn : ℝ} (hε : 0 < ε) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hK : 0 ≤ K) (hqn : 0 ≤ qn)
    (he : |a - L - Q| ≤ min 1 (ε / (2 * (|c| + 1))) * t ^ 2)
    (hQ : |Q| ≤ K / 2 * t ^ 2) (hL : |L| ≤ qn * t)
    (ht3 : t ≤ ε / (2 * (|η| * ((K / 2 + 1) * (K / 2 + 1 + 2 * qn)) + 1))) :
    |c * (a - L - Q) - η * (a ^ 2 - L ^ 2)| ≤ ε * t ^ 2 := by
  set ε₁ := min 1 (ε / (2 * (|c| + 1))) with hε₁
  set M := (K / 2 + 1) * (K / 2 + 1 + 2 * qn) with hM
  have hM0 : 0 ≤ M := by positivity
  have hε₁1 : ε₁ ≤ 1 := min_le_left _ _
  have hε₁2 : ε₁ ≤ ε / (2 * (|c| + 1)) := min_le_right _ _
  have ht2 : t ^ 2 ≤ t := by nlinarith
  -- |a - L| and |a - L + 2L|
  have hE : |a - L - Q| ≤ t ^ 2 := by
    have : ε₁ * t ^ 2 ≤ 1 * t ^ 2 := mul_le_mul_of_nonneg_right hε₁1 (by positivity)
    linarith
  have hD : |a - L| ≤ (K / 2 + 1) * t ^ 2 := by
    obtain ⟨e1, e2⟩ := abs_le.1 hE
    obtain ⟨q1, q2⟩ := abs_le.1 hQ
    rw [abs_le]; constructor <;> nlinarith
  have hD2 : |a - L + 2 * L| ≤ (K / 2 + 1) * t ^ 2 + 2 * qn * t := by
    obtain ⟨d1, d2⟩ := abs_le.1 hD
    obtain ⟨l1, l2⟩ := abs_le.1 hL
    rw [abs_le]; constructor <;> nlinarith
  -- the quadratic error
  have hprod : |a ^ 2 - L ^ 2| ≤ ((K / 2 + 1) * t ^ 2) * ((K / 2 + 1) * t ^ 2 + 2 * qn * t) := by
    rw [show a ^ 2 - L ^ 2 = (a - L) * (a - L + 2 * L) by ring, abs_mul]
    exact mul_le_mul hD hD2 (abs_nonneg _) (by positivity)
  have hprod2 : ((K / 2 + 1) * t ^ 2) * ((K / 2 + 1) * t ^ 2 + 2 * qn * t) ≤ M * t ^ 3 := by
    have h1 : (K / 2 + 1) * t ^ 2 + 2 * qn * t ≤ (K / 2 + 1 + 2 * qn) * t := by nlinarith
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (K / 2 + 1) * t ^ 2)
    rw [hM]
    nlinarith
  -- the two terms
  have hT1 : |c * (a - L - Q)| ≤ ε / 2 * t ^ 2 := by
    rw [abs_mul]
    have h1 : |c| * |a - L - Q| ≤ |c| * (ε₁ * t ^ 2) :=
      mul_le_mul_of_nonneg_left he (abs_nonneg c)
    have h2 : |c| * ε₁ ≤ ε / 2 := by
      have := mul_le_mul_of_nonneg_left hε₁2 (abs_nonneg c)
      have e : |c| * (ε / (2 * (|c| + 1))) ≤ ε / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [abs_nonneg c]
      linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ t ^ 2)
    nlinarith
  have hT2 : |η * (a ^ 2 - L ^ 2)| ≤ ε / 2 * t ^ 2 := by
    rw [abs_mul]
    have h1 : |η| * |a ^ 2 - L ^ 2| ≤ |η| * (M * t ^ 3) :=
      mul_le_mul_of_nonneg_left (hprod.trans hprod2) (abs_nonneg η)
    have h2 : |η| * M * t ≤ ε / 2 := by
      have := mul_le_mul_of_nonneg_left ht3 (by positivity : (0 : ℝ) ≤ |η| * M)
      have e : |η| * M * (ε / (2 * (|η| * M + 1))) ≤ ε / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [mul_nonneg (abs_nonneg η) hM0]
      linarith
    have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ t ^ 2)
    have e : |η| * (M * t ^ 3) = |η| * M * t * t ^ 2 := by ring
    linarith
  obtain ⟨a1, a2⟩ := abs_le.1 hT1
  obtain ⟨b1, b2⟩ := abs_le.1 hT2
  rw [abs_le]
  constructor <;> linarith

/-- **Composing an expansion with `ψ(s) = s - η s²`.** -/
theorem peanoAt_cv {V : EuclSpace d → ℝ} {x q : EuclSpace d} {X : Bilin d}
    (h : PeanoAt V x q X) (η : ℝ) :
    PeanoAt (fun y => V y - η * V y ^ 2) x ((1 - 2 * η * V x) • q)
      ((1 - 2 * η * V x) • X - (2 * η) • rankOne q) := by
  intro ε hε
  set c := 1 - 2 * η * V x with hc
  set K := ‖X‖ with hK
  set qn := ‖q‖ with hqn
  obtain ⟨δ₁, hδ₁, hb⟩ := h (min 1 (ε / (2 * (|c| + 1)))) (by positivity)
  refine ⟨min (min δ₁ 1) (ε / (2 * (|η| * ((K / 2 + 1) * (K / 2 + 1 + 2 * qn)) + 1))),
    by positivity, fun k hk => ?_⟩
  have hk1 : ‖k‖ < δ₁ := lt_of_lt_of_le hk (le_trans (min_le_left _ _) (min_le_left _ _))
  have hkle1 : ‖k‖ ≤ 1 := le_trans hk.le (le_trans (min_le_left _ _) (min_le_right _ _))
  have hk3 : ‖k‖ ≤ ε / (2 * (|η| * ((K / 2 + 1) * (K / 2 + 1 + 2 * qn)) + 1)) :=
    le_trans hk.le (min_le_right _ _)
  have he := hb k hk1
  -- the jet terms
  have hQ : inner ℝ (c • q) k = c * inner ℝ q k := real_inner_smul_left _ _ _
  have hR : ((c • X - (2 * η) • rankOne q) k) k = c * (X k) k - 2 * η * (inner ℝ q k * inner ℝ q k) := by
    rw [sub_apply, sub_apply, smul_apply, smul_apply, smul_apply, smul_apply, smul_eq_mul,
      smul_eq_mul, rankOne_apply]
  change |(V (x + k) - η * V (x + k) ^ 2) - (V x - η * V x ^ 2) - inner ℝ (c • q) k
    - 1 / 2 * ((c • X - (2 * η) • rankOne q) k) k| ≤ ε * ‖k‖ ^ 2
  rw [hQ, hR]
  have key : (V (x + k) - η * V (x + k) ^ 2) - (V x - η * V x ^ 2) - c * inner ℝ q k
      - 1 / 2 * (c * (X k) k - 2 * η * (inner ℝ q k * inner ℝ q k))
      = c * (V (x + k) - V x - inner ℝ q k - 1 / 2 * (X k) k)
        - η * ((V (x + k) - V x) ^ 2 - inner ℝ q k ^ 2) := by
    rw [hc]; ring
  rw [key]
  -- the bounds, in a small context
  have hQb : |1 / 2 * (X k) k| ≤ K / 2 * ‖k‖ ^ 2 := by
    have h1 : ‖(X k) k‖ ≤ ‖X‖ * ‖k‖ * ‖k‖ := X.le_opNorm₂ k k
    rw [Real.norm_eq_abs] at h1
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hK]
    nlinarith
  have hLb : |inner ℝ q k| ≤ qn * ‖k‖ := abs_real_inner_le_norm q k
  have e2 : V (x + k) - V x - inner ℝ q k - 1 / 2 * (X k) k
      = (V (x + k) - V x) - inner ℝ q k - 1 / 2 * (X k) k := rfl
  exact cv_arith hε (norm_nonneg k) hkle1 (norm_nonneg X) (norm_nonneg q) he hQb hLb hk3

end

end PLaplacian
