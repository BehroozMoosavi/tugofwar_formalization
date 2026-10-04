/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.ErrSmall

/-!
# The subsolution inequality in the regular case

At a strict maximum of the upper relaxed limit minus a bounded C three test
function with nonvanishing gradient, the normalized p-Laplacian of the test
function is nonnegative.

The proof is by contradiction and draws on everything the convergence layer
built: the near-maximizer measured against the parameter own supremum and
found frequently near the maximum by the annulus argument; the approximate
comparison carrying the slack; the expansion made uniform in the base point;
the error shown small against the squared parameter; and the continuity of
the operator away from the singular set.

Scope. This is the regular field for a bounded C three test function at a
strict maximum. The singular field, at which the gradient vanishes and the
expansion used here is unavailable, and the reduction of a general test
function --- non-strict maximum, unbounded, of class C two only --- to this
case, are not here.

## Main results

- regular_subsol
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The subsolution inequality in the regular case

At a strict maximum of the upper relaxed limit minus a bounded `C³` test
function, with nonvanishing gradient, the normalized `p`-Laplacian of the test
function is nonnegative.

By contradiction. Were it negative, say below `-γ`, continuity keeps it below
`-γ/2` near the maximum. The near-maximizer is frequently near the maximum;
there the approximate comparison and the uniform expansion give
`0 ≤ c N + E + ε³` with `c = ε²/(2(p+d))`. But `c N < -2ηε²`, `E ≤ ηε²` and
`ε³ < ηε²` for `η = γ/(8(p+d))` and small `ε`, which sums to a negative
number.

Scope. This is the regular field for a bounded `C³` test function at a strict
maximum. The singular field, and the reduction of a general test function ---
non-strict maximum, unbounded, of class `C²` only --- to this case, are not
here.
-/

/-- **The regular-case subsolution inequality.** -/
theorem regular_subsol [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε))
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ) (hφb : BddMeas φ)
    {B : ℝ} (hB : ∀ y, |φ y| ≤ B)
    {x₀ : EuclSpace d} {r : ℝ} (hr : 0 < r) (hΩ : closedBall x₀ r ⊆ Ω)
    (hstrict : IsStrictMaxOn (fun w => ubar u w - φ w) x₀ r)
    (hx₀ : gradient φ x₀ ≠ 0) :
    0 ≤ normPLapOf p (gradient φ x₀) (fderiv ℝ (fderiv ℝ φ) x₀) := by
  by_contra hneg
  push Not at hneg
  set N := fun y => normPLapOf p (gradient φ y) (fderiv ℝ (fderiv ℝ φ) y)
    with hNdef
  set γ := -N x₀ with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith
  -- continuity keeps the operator below -γ/2 near the maximum
  have hcont := normPLapOf_continuousAt (p := p) (hφ.of_le (by norm_num)) hx₀
  have hev1 : ∀ᶠ y in nhds x₀, N y < -γ / 2 :=
    hcont.eventually (eventually_lt_nhds (by rw [hγdef]; linarith))
  rw [Metric.eventually_nhds_iff] at hev1
  obtain ⟨ρ₁, hρ₁, hN⟩ := hev1
  -- the uniform expansion
  obtain ⟨ρ₂, hρ₂, H, K, Ka, g, _hg, _hK, _hH, _hKa, hexp⟩ :=
    expansion_uniform hd hp hpd hφ hx₀
  set η := γ / (8 * (p + (d : ℝ))) with hηdef
  have hη : 0 < η := by rw [hηdef]; positivity
  -- the radius for the near-maximizer
  set ρ := min (min ρ₁ ρ₂) (r / 2) with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]; exact lt_min (lt_min hρ₁ hρ₂) (by linarith)
  -- the near-maximizer as a function of the parameter
  have hex : ∀ ε : ℝ, 0 < ε → ∃ z ∈ closedBall x₀ r,
      sSup ((fun w => u ε w - φ w) '' closedBall x₀ r) - ε ^ 3
        < u ε z - φ z :=
    fun ε hε => exists_near_sup_cube u hC hB x₀ hr hε
  choose! y hymem hynear using hex
  have hfreq := nearmax_frequently_in_ball u hC hφ.continuous hB hr hρ
    hstrict y (fun ε hε => ⟨hymem ε hε, hynear ε hε⟩)
  -- the eventual conditions on the parameter
  have hsmall := eventually_bound_le (H := H) (K := K) (Ka := Ka) (g := g) hη
  have hlt : ∀ {a : ℝ}, 0 < a →
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < a := by
    intro a ha
    exact Filter.mem_of_superset (Ioo_mem_nhdsGT ha) (fun x hx => hx.2)
  have hpos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
    self_mem_nhdsWithin
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ((H * ε * Real.sqrt (2 * ε * ((H * ε ^ 2 + 2 * K * ε ^ 3) / g))
          + K * ε ^ 3) + Ka * ε ^ 3 ≤ η * ε ^ 2)
      ∧ ε < r / 2 ∧ ε < ρ₂ ∧ ε < η ∧ 0 < ε :=
    hsmall.and ((hlt (by linarith : (0:ℝ) < r / 2)).and
      ((hlt hρ₂).and ((hlt hη).and hpos)))
  -- a parameter satisfying all of it
  obtain ⟨ε, hyball, hbd, hεr, hερ₂, hεη, hε⟩ :=
    (hfreq.and_eventually hev).exists
  -- the near-maximizer's position
  have hyρ : dist (y ε) x₀ < ρ := hyball
  have hy₁ : y ε ∈ ball x₀ ρ₁ := by
    rw [mem_ball]
    exact lt_of_lt_of_le hyρ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hy₂ : y ε ∈ ball x₀ ρ₂ := by
    rw [mem_ball]
    exact lt_of_lt_of_le hyρ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hyr : dist (y ε) x₀ < r / 2 :=
    lt_of_lt_of_le hyρ (min_le_right _ _)
  -- the expansion at the near-maximizer
  obtain ⟨E, hTeq, hEbd⟩ := hexp (y ε) hy₂ ε hε (le_of_lt hερ₂)
  -- the approximate comparison at the near-maximizer
  have hyΩ : y ε ∈ Ω := hΩ (hymem ε hε)
  have hle : ∀ w ∈ ball (y ε) ε,
      u ε w - φ w ≤ sSup ((fun w => u ε w - φ w) '' closedBall x₀ r) := by
    intro w hw
    have hwc : w ∈ closedBall x₀ r := by
      rw [mem_closedBall]
      rw [mem_ball] at hw
      have := dist_triangle w (y ε) x₀
      linarith
    exact le_sup_on_ball u hC hB x₀ w hwc
  have hcmp := dpp_comparison_approx hp hε hpd (hu ε hε) hφb hyΩ hle
    (le_of_lt (hynear ε hε))
  -- combine
  rw [hTeq] at hcmp
  have hNy : N (y ε) < -γ / 2 := hN hy₁
  have hc : 0 < ε ^ 2 / (2 * (p + (d : ℝ))) := by positivity
  have hε2 : 0 < ε ^ 2 := by positivity
  have hcγ : ε ^ 2 / (2 * (p + (d : ℝ))) * (γ / 2) = 2 * η * ε ^ 2 := by
    rw [hηdef]; field_simp; ring
  have h1 : ε ^ 2 / (2 * (p + (d : ℝ))) * N (y ε) < -(2 * η * ε ^ 2) := by
    have := mul_lt_mul_of_pos_left hNy hc
    linarith [this, hcγ]
  have h2 : E ≤ η * ε ^ 2 := le_trans (le_abs_self E) (le_trans hEbd hbd)
  have h3 : ε ^ 3 < η * ε ^ 2 := by
    have : ε * ε ^ 2 < η * ε ^ 2 := mul_lt_mul_of_pos_right hεη hε2
    nlinarith [this]
  have h4 : 0 ≤ ε ^ 2 / (2 * (p + (d : ℝ))) * N (y ε) + E + ε ^ 3 := by
    simp only [hNdef] at h1 ⊢
    linarith [hcmp]
  linarith [h1, h2, h3, h4]

end

end PLaplacian
