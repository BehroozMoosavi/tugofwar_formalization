/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Plaplacian.DomainBounds

@[expose] public section

/-!
# The three bounds of the uniform convergence argument

`deficitLimit_le_zero` reduces uniform convergence to producing, for each
positive `delta`, the three chained bounds of `unif_arith`. This file proves
each of them.

* `bound_one` is the chained estimate. `key_estimate` compares the operator at
  two iterates, and monotonicity then replaces the later iterate by the limit
  in both the supremum and the average term.

* `bound_two` bounds the supremum over a ball by `M + delta`. Note that the
  deficit supremum must be taken over `closureEps`, not over the domain: the
  supremum in the chained estimate ranges over a ball centred at a point of the
  domain, and such a ball reaches into the boundary strip. This is what
  `ball_subset_closureEps` supplies.

* `bound_three` bounds the average term. The local average over a ball is
  dominated by the global integral over `closureEps` divided by the
  centre-independent ball volume, and that global integral is made small by
  `tendsto_setIntegral_deficit`. `bound_three_eta` computes the explicit target
  for the global integral that makes the conclusion exactly `delta`.

## Main results

- `bound_one`, `bound_two`, `bound_three`, `bound_three_eta`
-/

open MeasureTheory Metric Set Filter

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-- **The chained estimate.** -/
theorem bound_one (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ))
    {u wl wk : EuclSpace d → ℝ}
    (hu : BddMeas u) (hwl : BddMeas wl) (hwk : BddMeas wk)
    (hlu : ∀ y, wl y ≤ u y)
    {C : ℝ} (hC : ∀ y, |u y - wk y| ≤ C)
    (x₀ : EuclSpace d) :
    tugOfWarOp p ε wl x₀ - tugOfWarOp p ε wk x₀
      ≤ (p - 2) / (p + (d : ℝ))
          * sSup ((fun y => u y - wk y) '' ball x₀ ε)
        + ((d : ℝ) + 2) / (p + (d : ℝ))
            * ⨍ y in ball x₀ ε, (u y - wk y) := by
  have hkey := key_estimate p ε hp hε hpd hwk hwl x₀
  have hα : (0 : ℝ) ≤ (p - 2) / (p + (d : ℝ)) :=
    div_nonneg (by linarith) hpd.le
  have hβ : (0 : ℝ) ≤ ((d : ℝ) + 2) / (p + (d : ℝ)) := by positivity
  have hsup : sSup ((fun y => wl y - wk y) '' ball x₀ ε)
      ≤ sSup ((fun y => u y - wk y) '' ball x₀ ε) :=
    sSup_diff_mono (nonempty_ball x₀ hε) hlu hC
  have havg : (⨍ y in ball x₀ ε, (wl y - wk y))
      ≤ ⨍ y in ball x₀ ε, (u y - wk y) :=
    setAverage_diff_mono hlu x₀
      ((hwl.sub hwk).integrableOn_ball x₀ ε)
      ((hu.sub hwk).integrableOn_ball x₀ ε)
  have h1 := mul_le_mul_of_nonneg_left hsup hα
  have h2 := mul_le_mul_of_nonneg_left havg hβ
  linarith [hkey, h1, h2]

/-- **The supremum bound.** Needs `ball_subset_closureEps`, since the ball is
not contained in the domain. -/
theorem bound_two {Ω : Set (EuclSpace d)} {ε : ℝ}
    {u w : EuclSpace d → ℝ} {M δ C : ℝ}
    (hC : ∀ x, |u x - w x| ≤ C)
    (hk : deficitSup (closureEps Ω ε) u w ≤ M + δ)
    {x₀ : EuclSpace d} (hx₀ : x₀ ∈ Ω) (hε : 0 < ε) :
    sSup ((fun y => u y - w y) '' ball x₀ ε) ≤ M + δ := by
  refine csSup_le ⟨u x₀ - w x₀, x₀, mem_ball_self hε, rfl⟩ ?_
  rintro a ⟨y, hy, rfl⟩
  have hmem : y ∈ closureEps Ω ε := ball_subset_closureEps Ω hx₀ hy
  exact le_trans (le_csSup (bddAbove_deficit hC) ⟨y, hmem, rfl⟩) hk

/-- **The average bound.** -/
theorem bound_three {Ω : Set (EuclSpace d)} {ε : ℝ} (hε : 0 < ε)
    {u w : EuclSpace d → ℝ}
    (hnn : ∀ y, 0 ≤ u y - w y)
    (hint : MeasureTheory.IntegrableOn (fun y => u y - w y) (closureEps Ω ε))
    {x₀ : EuclSpace d} (hx₀ : x₀ ∈ Ω)
    {β η : ℝ} (hβ : 0 ≤ β)
    (hsmall : (∫ y in closureEps Ω ε, (u y - w y)) ≤ η) :
    β * (⨍ y in ball x₀ ε, (u y - w y))
      ≤ β * ((volume.real (ball (0 : EuclSpace d) ε))⁻¹ * η) := by
  refine mul_le_mul_of_nonneg_left ?_ hβ
  refine le_trans (setAverage_le_integral_div _ hnn hint x₀ hε
    (ball_subset_closureEps Ω hx₀)) ?_
  have hpos : (0 : ℝ) ≤ (volume.real (ball (0 : EuclSpace d) ε))⁻¹ := by
    positivity
  exact mul_le_mul_of_nonneg_left hsmall hpos

/-- The target for the global integral making the average bound exactly
`delta`. -/
theorem bound_three_eta {β δ : ℝ} (hβ : 0 < β) {ε : ℝ}
    (hvol : (0 : ℝ) < volume.real (ball (0 : EuclSpace d) ε)) (hδ : 0 < δ) :
    0 < δ * volume.real (ball (0 : EuclSpace d) ε) / β
    ∧ β * ((volume.real (ball (0 : EuclSpace d) ε))⁻¹
        * (δ * volume.real (ball (0 : EuclSpace d) ε) / β)) = δ := by
  refine ⟨by positivity, ?_⟩
  field_simp

end

end PLaplacian
