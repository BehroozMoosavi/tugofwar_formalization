/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.DirichletExistence

/-!
# Uniqueness for the `ε`-problem

Two `p`-harmonious functions in a bounded set `Ω` that agree outside `Ω` agree
everywhere. The difference `w = v - u` may not attain its supremum `M`, so
instead of evaluating the equation at a maximum point we follow near-maxima.

* **One step.** If `w(x) > M - δ` at `x ∈ Ω`, the dynamic programming principle
  forces the average of `w` over `B_ε(x)` to exceed `M - δ / β`. A small ball
  `S` near the edge of `B_ε(x)`, in a fixed direction `e`, occupies a fixed
  fraction of `B_ε(x)`; hence `w > M - Cδ` somewhere in `S`, at a point lying
  at least `ε / 2` further in the direction `e`.
* **The walk.** Starting from `w(x₀) > M - δ₀` and repeating the step, the
  points move in the direction `e` by `ε / 2` each time, so after finitely many
  steps they leave the bounded set `Ω`, where `w = 0`. With `δ₀` small, the last
  point still has `w > M / 2 > 0`: a contradiction unless `M ≤ 0`.

## Main results

- `disc_step`: the one-step estimate.
- `sup_diff_nonpos`: the difference of two solutions is nonpositive.
- `pharmonious_unique`: uniqueness for the `ε`-problem with exterior data.
-/

/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/



open MeasureTheory Metric Set Filter
open scoped RealInnerProductSpace

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-- The constant of the one-step estimate: `2 |B_ε| / (β |B_{ε/4}|)`. -/
def stepConst (p ε : ℝ) : ℝ :=
  2 * volume.real (ball (0 : EuclSpace d) ε)
    / (((d : ℝ) + 2) / (p + (d : ℝ))
        * volume.real (ball (0 : EuclSpace d) (ε / 4)))

theorem volumeReal_ball_pos {r : ℝ} (hr : 0 < r) :
    0 < volume.real (ball (0 : EuclSpace d) r) := by
  have h1 : volume (ball (0 : EuclSpace d) r) ≠ 0 := measure_ball_ne_zero 0 hr
  have h2 : volume (ball (0 : EuclSpace d) r) ≠ ⊤ := measure_ball_lt_top.ne
  simp only [MeasureTheory.Measure.real]
  exact ENNReal.toReal_pos h1 h2

theorem integrableOn_const_ball (c : ℝ) (x : EuclSpace d) (r : ℝ) :
    IntegrableOn (fun _ : EuclSpace d => c) (ball x r) := by
  refine MeasureTheory.integrableOn_const ?_ ?_
  · exact measure_ball_lt_top.ne
  · simp

/-- The arithmetic at the end of the one-step estimate. -/
theorem step_arith {M δ a b A V K s : ℝ} (hb : 0 < b) (hV : 0 < V)
    (hδ : 0 < δ) (hab : a + b = 1) (hw : M - δ < a * M + b * A)
    (hK : K * δ * s = 2 * V * δ / b) (hint : K * δ * s ≤ V * (M - A)) :
    False := by
  have ha : a * M = M - b * M := by
    have : a = 1 - b := by linarith
    rw [this]; ring
  have h1 : b * (M - A) < δ := by nlinarith
  have h2 : V * (b * (M - A)) < V * δ := mul_lt_mul_of_pos_left h1 hV
  have h3 : 2 * V * δ / b ≤ V * (M - A) := by rw [← hK]; exact hint
  have h4 : 2 * V * δ ≤ V * (M - A) * b := (div_le_iff₀ hb).1 h3
  have h5 : 0 < V * δ := mul_pos hV hδ
  nlinarith

/-- **The one-step estimate.** If `v - u ≤ M` everywhere and `v x - u x > M - δ`
at a point `x ∈ Ω`, then `v - u > M - Cδ` at some point `y` with
`⟪y, e⟫ ≥ ⟪x, e⟫ + ε / 2`. -/
theorem disc_step (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)}
    {u v : EuclSpace d → ℝ} (hu : BddMeas u) (hv : BddMeas v)
    (hTu : ∀ x ∈ Ω, u x = tugOfWarOp p ε u x)
    (hTv : ∀ x ∈ Ω, v x = tugOfWarOp p ε v x)
    {M : ℝ} (hM : ∀ y, v y - u y ≤ M)
    {x : EuclSpace d} (hx : x ∈ Ω) {δ : ℝ} (hδ : 0 < δ)
    (hwx : M - δ < v x - u x) {e : EuclSpace d} (he : ‖e‖ = 1) :
    ∃ y, M - stepConst (d := d) p ε * δ < v y - u y
      ∧ ⟪x, e⟫ + ε / 2 ≤ ⟪y, e⟫ := by
  have hβ : 0 < ((d : ℝ) + 2) / (p + (d : ℝ)) := by positivity
  have hα : 0 ≤ (p - 2) / (p + (d : ℝ)) := div_nonneg (by linarith) hpd.le
  have hab := alpha_add_beta p hpd
  have hV : 0 < volume.real (ball (0 : EuclSpace d) ε) := volumeReal_ball_pos hε
  have hs : 0 < volume.real (ball (0 : EuclSpace d) (ε / 4)) :=
    volumeReal_ball_pos (by linarith)
  have hw : BddMeas (fun y => v y - u y) := hv.sub hu
  -- the equation at x
  have hkey := key_estimate p ε hp hε hpd hu hv x
  have hsup : sSup ((fun y => v y - u y) '' ball x ε) ≤ M := by
    refine csSup_le ((nonempty_ball x hε).image _) ?_
    rintro _ ⟨y, -, rfl⟩
    exact hM y
  have hwx' : v x - u x ≤ (p - 2) / (p + (d : ℝ)) * M
      + ((d : ℝ) + 2) / (p + (d : ℝ)) * ⨍ y in ball x ε, (v y - u y) := by
    have h1 : v x - u x = tugOfWarOp p ε v x - tugOfWarOp p ε u x := by
      rw [← hTv x hx, ← hTu x hx]
    have h2 := mul_le_mul_of_nonneg_left hsup hα
    rw [h1]
    linarith [hkey]
  -- the small ball near the edge of B_ε(x), in the direction e
  set c := x + (3 * ε / 4) • e with hcdef
  have hcx : ‖c - x‖ = 3 * ε / 4 := by
    rw [hcdef, add_sub_cancel_left, norm_smul, he, mul_one, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
  have hSB : ball c (ε / 4) ⊆ ball x ε := by
    intro y hy
    rw [mem_ball] at hy ⊢
    calc dist y x ≤ dist y c + dist c x := dist_triangle _ _ _
      _ < ε / 4 + 3 * ε / 4 := by
          rw [dist_eq_norm c x, hcx]; linarith
      _ = ε := by ring
  -- every point of the small ball lies far enough in the direction e
  have hfar : ∀ y ∈ ball c (ε / 4), ⟪x, e⟫ + ε / 2 ≤ ⟪y, e⟫ := by
    intro y hy
    have hyc : ‖y - c‖ < ε / 4 := by rw [← dist_eq_norm]; exact mem_ball.1 hy
    have h5 : -(ε / 4) ≤ ⟪y - c, e⟫ := by
      have := abs_real_inner_le_norm (y - c) e
      rw [he, mul_one] at this
      linarith [neg_abs_le ⟪y - c, e⟫]
    have h6 : ⟪c, e⟫ = ⟪x, e⟫ + 3 * ε / 4 := by
      rw [hcdef, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, he]
      ring
    have h7 : ⟪y, e⟫ = ⟪y - c, e⟫ + ⟪c, e⟫ := by
      rw [← inner_add_left, sub_add_cancel]
    linarith
  -- by contradiction: no point of the small ball has v - u > M - Cδ
  by_contra hcon
  push Not at hcon
  have hlow : ∀ y ∈ ball c (ε / 4),
      stepConst (d := d) p ε * δ ≤ M - (v y - u y) := by
    intro y hy
    by_contra hlt
    push Not at hlt
    have := hcon y (by linarith)
    linarith [hfar y hy]
  -- integrate over the small ball and over B_ε(x)
  have hintB : IntegrableOn (fun y => M - (v y - u y)) (ball x ε) :=
    Integrable.sub (integrableOn_const_ball M x ε) (hw.integrableOn_ball x ε)
  have hintS : IntegrableOn (fun y => M - (v y - u y)) (ball c (ε / 4)) :=
    hintB.mono_set hSB
  have hnn : ∀ y, 0 ≤ M - (v y - u y) := fun y => by linarith [hM y]
  have hI1 : (∫ y in ball c (ε / 4), (M - (v y - u y)))
      ≤ ∫ y in ball x ε, (M - (v y - u y)) :=
    MeasureTheory.setIntegral_mono_set hintB
      (Filter.Eventually.of_forall hnn) (LE.le.eventuallyLE hSB)
  have hI2 : (∫ y in ball c (ε / 4), (stepConst (d := d) p ε * δ))
      ≤ ∫ y in ball c (ε / 4), (M - (v y - u y)) :=
    MeasureTheory.setIntegral_mono_on (integrableOn_const_ball _ c _) hintS
      measurableSet_ball hlow
  have hI3 : (∫ y in ball c (ε / 4), (stepConst (d := d) p ε * δ))
      = stepConst (d := d) p ε * δ
          * volume.real (ball (0 : EuclSpace d) (ε / 4)) := by
    rw [MeasureTheory.setIntegral_const, smul_eq_mul,
      volumeReal_ball_center c (ε / 4)]
    ring
  have hI4 : (∫ y in ball x ε, (M - (v y - u y)))
      = volume.real (ball (0 : EuclSpace d) ε)
          * (M - ⨍ y in ball x ε, (v y - u y)) := by
    rw [MeasureTheory.integral_sub (integrableOn_const_ball M x ε)
        (hw.integrableOn_ball x ε),
      MeasureTheory.setIntegral_const, smul_eq_mul,
      MeasureTheory.setAverage_eq, smul_eq_mul, volumeReal_ball_center x ε,
      mul_sub, ← mul_assoc, mul_inv_cancel₀ hV.ne', one_mul]
  have hint : stepConst (d := d) p ε * δ
        * volume.real (ball (0 : EuclSpace d) (ε / 4))
      ≤ volume.real (ball (0 : EuclSpace d) ε)
          * (M - ⨍ y in ball x ε, (v y - u y)) := by
    rw [← hI3, ← hI4]; exact le_trans hI2 hI1
  have hK : stepConst (d := d) p ε * δ
        * volume.real (ball (0 : EuclSpace d) (ε / 4))
      = 2 * volume.real (ball (0 : EuclSpace d) ε) * δ
          / (((d : ℝ) + 2) / (p + (d : ℝ))) := by
    have hsne := hs.ne'
    have hβne := hβ.ne'
    have hpdne : p + (d : ℝ) ≠ 0 := hpd.ne'
    have hd2 : (d : ℝ) + 2 ≠ 0 := by positivity
    unfold stepConst
    field_simp
  exact step_arith hβ hV hδ hab (lt_of_lt_of_le hwx hwx') hK hint

/-- **The difference of two solutions is nonpositive.** If `u` and `v` satisfy
the dynamic programming principle in a bounded set `Ω` and agree outside `Ω`,
then `v ≤ u`. -/
theorem sup_diff_nonpos [Nontrivial (EuclSpace d)] (p ε : ℝ) (hp : 2 ≤ p)
    (hε : 0 < ε) (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)}
    (hΩb : Bornology.IsBounded Ω)
    {u v : EuclSpace d → ℝ} (hu : BddMeas u) (hv : BddMeas v)
    (hTu : ∀ x ∈ Ω, u x = tugOfWarOp p ε u x)
    (hTv : ∀ x ∈ Ω, v x = tugOfWarOp p ε v x)
    (hout : ∀ x, x ∉ Ω → u x = v x) :
    ∀ x, v x ≤ u x := by
  have hw : BddMeas (fun y => v y - u y) := hv.sub hu
  obtain ⟨B, hB⟩ := hw.bound
  have hbdd : BddAbove (range fun y => v y - u y) :=
    ⟨B, by rintro _ ⟨y, rfl⟩; exact (abs_le.1 (hB y)).2⟩
  set M := ⨆ y, (v y - u y)
  have hM : ∀ y, v y - u y ≤ M := fun y => le_ciSup hbdd y
  -- it suffices to show M ≤ 0
  suffices hM0 : M ≤ 0 by
    intro x
    linarith [hM x]
  by_contra hMpos
  push Not at hMpos
  -- a point where v - u > 0 lies in Ω
  have hmem : ∀ y, 0 < v y - u y → y ∈ Ω := by
    intro y hy
    by_contra hyΩ
    rw [hout y hyΩ, sub_self] at hy
    exact lt_irrefl _ hy
  -- a unit direction, and a bound for Ω in that direction
  obtain ⟨e, he⟩ := exists_norm_eq (EuclSpace d) zero_le_one
  obtain ⟨R, hR⟩ := hΩb.exists_norm_le
  have hproj : ∀ y ∈ Ω, |⟪y, e⟫| ≤ R := by
    intro y hy
    have := abs_real_inner_le_norm y e
    rw [he, mul_one] at this
    exact le_trans this (hR y hy)
  -- the number of steps and the constants
  set C := max (stepConst (d := d) p ε) 1
  have hC1 : 1 ≤ C := le_max_right _ _
  have hCpos : 0 < C := by linarith
  set N : ℕ := ⌈4 * |R| / ε⌉₊ + 1 with hNdef
  have hCN : 0 < C ^ N := pow_pos hCpos N
  set δ₀ := M / (2 * C ^ N) with hδ₀def
  have hδ₀ : 0 < δ₀ := by rw [hδ₀def]; positivity
  have hsmall : ∀ k ≤ N, C ^ k * δ₀ ≤ M / 2 := by
    intro k hk
    have h1 : C ^ k ≤ C ^ N := pow_le_pow_right₀ hC1 hk
    have hCNne : C ^ N ≠ 0 := hCN.ne'
    have h2 : C ^ N * δ₀ = M / 2 := by
      rw [hδ₀def]
      field_simp
    calc C ^ k * δ₀ ≤ C ^ N * δ₀ := mul_le_mul_of_nonneg_right h1 hδ₀.le
      _ = M / 2 := h2
  -- the starting point
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, M - δ₀ < v x₀ - u x₀ :=
    exists_lt_of_lt_ciSup (by linarith : M - δ₀ < M)
  -- the walk
  have hwalk : ∀ k ≤ N, ∃ x, M - C ^ k * δ₀ < v x - u x
      ∧ ⟪x₀, e⟫ + (k : ℝ) * (ε / 2) ≤ ⟪x, e⟫ := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨x₀, ?_, ?_⟩
        · simpa using hx₀
        · simp
    | succ k ih =>
        intro hk
        obtain ⟨x, hxw, hxe⟩ := ih (Nat.le_of_succ_le hk)
        have hk' := hsmall k (Nat.le_of_succ_le hk)
        have hxΩ : x ∈ Ω := hmem x (by linarith)
        have hδk : 0 < C ^ k * δ₀ := by positivity
        obtain ⟨y, hyw, hye⟩ :=
          disc_step p ε hp hε hpd hu hv hTu hTv hM hxΩ hδk hxw he
        refine ⟨y, ?_, ?_⟩
        · have h1 : stepConst (d := d) p ε ≤ C := le_max_left _ _
          have h2 : stepConst (d := d) p ε * (C ^ k * δ₀) ≤ C * (C ^ k * δ₀) :=
            mul_le_mul_of_nonneg_right h1 hδk.le
          have h3 : C ^ (k + 1) * δ₀ = C * (C ^ k * δ₀) := by rw [pow_succ]; ring
          rw [h3]
          linarith
        · push_cast
          linarith
  -- after N steps the walk has left Ω, but v - u is still positive there
  obtain ⟨x, hxw, hxe⟩ := hwalk N le_rfl
  have hxΩ : x ∈ Ω := hmem x (by linarith [hsmall N le_rfl])
  have hx₀Ω : x₀ ∈ Ω := hmem x₀ (by
    have := hsmall 0 (Nat.zero_le N)
    simp only [pow_zero, one_mul] at this
    linarith)
  obtain ⟨h1a, h1b⟩ := abs_le.1 (hproj x hxΩ)
  obtain ⟨h2a, h2b⟩ := abs_le.1 (hproj x₀ hx₀Ω)
  have hN : 4 * |R| / ε < (N : ℝ) := by
    rw [hNdef]; push_cast
    linarith [Nat.le_ceil (4 * |R| / ε)]
  have hNε : 2 * |R| < (N : ℝ) * (ε / 2) := by
    have := (div_lt_iff₀ hε).1 hN
    linarith
  have hRabs : R ≤ |R| := le_abs_self R
  linarith

/-- **Uniqueness for the `ε`-problem.** Two `p`-harmonious functions in a bounded
set `Ω` with data `F` that both equal `F` outside `Ω` are equal. -/
theorem pharmonious_unique [Nontrivial (EuclSpace d)] (p ε : ℝ) (hp : 2 ≤ p)
    (hε : 0 < ε) (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)}
    (hΩb : Bornology.IsBounded Ω) {F u v : EuclSpace d → ℝ}
    (hu : IsPHarmonious p ε Ω F u) (hv : IsPHarmonious p ε Ω F v)
    (huF : ∀ x, x ∉ Ω → u x = F x) (hvF : ∀ x, x ∉ Ω → v x = F x) :
    u = v := by
  have hout : ∀ x, x ∉ Ω → u x = v x := fun x hx => by rw [huF x hx, hvF x hx]
  have h1 := sup_diff_nonpos p ε hp hε hpd hΩb hu.bddMeas hv.bddMeas
    hu.interior hv.interior hout
  have h2 := sup_diff_nonpos p ε hp hε hpd hΩb hv.bddMeas hu.bddMeas
    hv.interior hu.interior (fun x hx => (hout x hx).symm)
  funext x
  exact le_antisymm (h2 x) (h1 x)

end

end PLaplacian
