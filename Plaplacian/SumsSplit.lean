/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.IshiiFoundations

/-! # The theorem of sums, split

The theorem of sums has two cases, according as the maximum of the doubled
function lies on the diagonal or off it, and they are of entirely different
difficulty.

## On the diagonal: trivial

If `u x - v y - ‖x - y‖⁴ / (4α)` is locally maximal at `(x̂, x̂)`, freezing
`y = x̂` gives `u x ≤ u x̂ + ‖x - x̂‖⁴ / (4α)` near `x̂`, and the quartic is
`o(‖x - x̂‖²)`; so `(0, 0)` is a superjet of `u`. Freezing `x = x̂` makes
`(0, 0)` a subjet of `v`. The forms `X = Y = 0` satisfy every conclusion. No
sup-convolution, Jensen or Alexandrov is needed.

## Off the diagonal: the real theorem

Freezing one variable at a time gives `X = D²g` and `Y = -D²g` for the convex
`g = ‖·‖⁴/(4α)`, so `X ≥ Y` --- the wrong direction. Obtaining `X ≤ Y` requires
the two variables to be treated jointly, which is what the theorem of sums
does. That case is isolated here as `TheoremOfSumsRegular`, the only hypothesis
that remains.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- **The regular half of the theorem of sums**, off the diagonal. -/
def TheoremOfSumsRegular (d : ℕ) : Prop :=
  ∀ (u v : EuclSpace d → ℝ), UpperSemicontinuous u → LowerSemicontinuous v →
    BddAbove (range u) → BddBelow (range v) →
    ∀ α : ℝ, 0 < α → ∀ xh yh : EuclSpace d, xh ≠ yh →
      IsLocalMax
        (fun z : EuclSpace d × EuclSpace d =>
          u z.1 - v z.2 - ‖z.1 - z.2‖ ^ 4 / (4 * α)) (xh, yh) →
      ∃ X Y : Bilin d,
        (penaltyGrad α xh yh, X) ∈ ClSuperJet u xh ∧
        (penaltyGrad α xh yh, Y) ∈ ClSubJet v yh ∧
        QuadLE X Y

/-- The quartic is eventually below any multiple of the square. -/
theorem eventually_quartic_le {x : EuclSpace d} {α η : ℝ} (hα : 0 < α)
    (hη : 0 < η) :
    ∀ᶠ y in 𝓝 x, ‖y - x‖ ^ 4 / (4 * α) ≤ η * ‖y - x‖ ^ 2 := by
  have hr : (0:ℝ) < 4 * α * η := by positivity
  filter_upwards [Metric.ball_mem_nhds x (Real.sqrt_pos.2 hr)] with y hy
  rw [mem_ball, dist_eq_norm] at hy
  have hn : (0:ℝ) ≤ ‖y - x‖ := norm_nonneg _
  have hsq : ‖y - x‖ ^ 2 ≤ 4 * α * η := by
    have h1 : ‖y - x‖ ^ 2 < (Real.sqrt (4 * α * η)) ^ 2 :=
      pow_lt_pow_left₀ hy hn (by norm_num)
    rw [Real.sq_sqrt hr.le] at h1
    exact h1.le
  have h4α : (0:ℝ) < 4 * α := by positivity
  rw [div_le_iff₀ h4α]
  have h2 : (0:ℝ) ≤ ‖y - x‖ ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsq h2]

/-- **On the diagonal, `(0, 0)` is a superjet of `u`.** -/
theorem superJet_zero_of_diag {u v : EuclSpace d → ℝ} {α : ℝ} (hα : 0 < α)
    {xh : EuclSpace d}
    (hmax : IsLocalMax
      (fun z : EuclSpace d × EuclSpace d =>
        u z.1 - v z.2 - ‖z.1 - z.2‖ ^ 4 / (4 * α)) (xh, xh)) :
    ((0 : EuclSpace d), (0 : Bilin d)) ∈ SuperJet u xh := by
  intro η hη
  have hslice : Tendsto (fun x : EuclSpace d => (x, xh)) (𝓝 xh) (𝓝 (xh, xh)) :=
    (continuous_id.prodMk continuous_const).tendsto xh
  have h1 := hslice.eventually hmax
  have h2 := eventually_quartic_le (x := xh) hα hη
  filter_upwards [h1, h2] with x hx hq
  simp only [inner_zero_left, zero_apply, mul_zero,
    add_zero]
  have hself : ‖xh - xh‖ ^ 4 / (4 * α) = 0 := by simp
  rw [hself] at hx
  linarith

/-- **On the diagonal, `(0, 0)` is a subjet of `v`.** -/
theorem subJet_zero_of_diag {u v : EuclSpace d → ℝ} {α : ℝ} (hα : 0 < α)
    {xh : EuclSpace d}
    (hmax : IsLocalMax
      (fun z : EuclSpace d × EuclSpace d =>
        u z.1 - v z.2 - ‖z.1 - z.2‖ ^ 4 / (4 * α)) (xh, xh)) :
    ((0 : EuclSpace d), (0 : Bilin d)) ∈ SubJet v xh := by
  intro η hη
  have hslice : Tendsto (fun y : EuclSpace d => (xh, y)) (𝓝 xh) (𝓝 (xh, xh)) :=
    (continuous_const.prodMk continuous_id).tendsto xh
  have h1 := hslice.eventually hmax
  have h2 := eventually_quartic_le (x := xh) hα hη
  filter_upwards [h1, h2] with y hy hq
  simp only [inner_zero_left, zero_apply, mul_zero,
    add_zero]
  have hself : ‖xh - xh‖ ^ 4 / (4 * α) = 0 := by simp
  rw [hself] at hy
  have hsym : ‖xh - y‖ = ‖y - xh‖ := norm_sub_rev xh y
  rw [hsym] at hy
  linarith

/-- **The theorem of sums, from its regular half.** -/
theorem theoremOfSums_of_regular (hreg : TheoremOfSumsRegular d) :
    TheoremOfSums d := by
  intro u v hu hv hub hvb α hα xh yh hmax
  by_cases heq : xh = yh
  · -- on the diagonal: the zero forms
    subst heq
    refine ⟨0, 0, ?_, ?_, QuadLE.refl 0, fun _ => ⟨QuadLE.refl 0, QuadLE.refl 0⟩⟩
    · rw [penaltyGrad_self]
      exact superJet_subset_cl u xh (superJet_zero_of_diag hα hmax)
    · rw [penaltyGrad_self]
      exact subJet_subset_cl v xh (subJet_zero_of_diag hα hmax)
  · -- off the diagonal: the regular half
    obtain ⟨X, Y, hX, hY, hXY⟩ := hreg u v hu hv hub hvb α hα xh yh heq hmax
    exact ⟨X, Y, hX, hY, hXY, fun h => absurd h heq⟩

/-- **The comparison principle for strict subsolutions, assuming only the
regular half of the theorem of sums.** -/
theorem comparison_strict_of_regular (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p)
    (hreg : TheoremOfSumsRegular d) {Ω : Set (EuclSpace d)} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {U V : EuclSpace d → ℝ}
    (hU : UpperSemicontinuous U) (hV : LowerSemicontinuous V)
    (hUb : BddAbove (range U)) (hVb : BddBelow (range V))
    {c : ℝ} (hc : 0 < c)
    (hsub : IsViscositySubsolution p Ω (fun _ => -c) U)
    (hsup : IsViscositySupersolution p Ω (fun _ => 0) V)
    (hbd : ∀ x ∈ frontier Ω, U x ≤ V x) :
    ∀ x ∈ Ω, U x ≤ V x :=
  comparison_strict hd hp (theoremOfSums_of_regular hreg) hΩo hΩb hU hV hUb hVb
    hc hsub hsup hbd

end

end PLaplacian
