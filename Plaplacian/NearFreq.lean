/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.SupFreq

/-!
# The near-maximizer is frequently near the base point

The convergence of the near-maximizers, obtained without extracting a
sequence. At a strict maximum there is a gap on the annulus; eventually the
family lies below the maximum less half the gap there; frequently the
parameter's own supremum exceeds the maximum less a quarter of it; and
eventually the cube of the parameter is below a quarter of it. So frequently
the near-maximizer's value exceeds the maximum less half the gap, which
excludes it from the annulus and places it within the inner radius.

The standard argument passes to a subsequence and uses compactness to extract
a limit point. This one uses compactness once, on the annulus, to make a
pointwise bound uniform, and otherwise works along the filter throughout. That
matches the library's grain and avoids the diagonalisation a sequential form
would need.

## Main results

- eventually_cube_lt
- nearmax_frequently_in_ball
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The near-maximizer is frequently near the base point

Combining the annulus route. At a strict maximum there is a gap `η` on the
annulus; eventually the family is below `M - η/2` there; frequently the
parameter's supremum exceeds `M - η/4`; eventually `ε³ < η/4`. So frequently
the near-maximizer's value exceeds `M - η/2`, which excludes it from the
annulus and puts it within the inner radius.

The near-maximizer is supplied as a function by hypothesis, so that its choice
is separate from the filter work.
-/


/-- The cube of the parameter is eventually below any positive bound. -/
theorem eventually_cube_lt {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε ^ 3 < τ := by
  have hc : Filter.Tendsto (fun ε : ℝ => ε ^ 3) (nhds 0) (nhds 0) := by
    have h := (continuous_pow 3).tendsto (0 : ℝ)
    simpa using h
  exact (hc.mono_left nhdsWithin_le_nhds).eventually (eventually_lt_nhds hτ)

/-- **The near-maximizer is frequently within any radius of the base
point.** -/
theorem nearmax_frequently_in_ball (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {φ : EuclSpace d → ℝ}
    (hφ : Continuous φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B)
    {x₀ : EuclSpace d} {r ρ : ℝ} (hr : 0 < r) (hρ : 0 < ρ)
    (hstrict : IsStrictMaxOn (fun w => ubar u w - φ w) x₀ r)
    (y : ℝ → EuclSpace d)
    (hy : ∀ ε > 0, y ε ∈ closedBall x₀ r ∧
      supBall u φ x₀ r ε - ε ^ 3 < u ε (y ε) - φ (y ε)) :
    ∃ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), y ε ∈ ball x₀ ρ := by
  -- the gap on the annulus
  obtain ⟨η, hη, hgap⟩ := annulus_gap u hC hφ hρ hstrict
  set M := ubar u x₀ - φ x₀ with hM
  -- the family below M - η/2 on the annulus, eventually
  have hgap' : ∀ w ∈ annulus x₀ ρ r, ubar u w - φ w < M - η / 2 := by
    intro w hw; have := hgap w hw; linarith [this, hη]
  obtain ⟨S, hS, hbdS⟩ := uniform_bound_annulus u hC hφ hB hgap'
  -- the supremum frequently above M - η/4
  have hsup := frequently_supBall_large u hC hφ hB x₀ hr
    (by linarith : (0:ℝ) < η / 4)
  -- the cube eventually below η/4, and the parameter positive
  have hcube := eventually_cube_lt (by linarith : (0:ℝ) < η / 4)
  have hpos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
    self_mem_nhdsWithin
  -- combine
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ε ∈ S ∧ ε ^ 3 < η / 4 ∧ 0 < ε :=
    ((show ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε ∈ S from hS).and
      (hcube.and hpos))
  refine (hsup.and_eventually hev).mono ?_
  rintro ε ⟨hsupε, hεS, hεcube, hεpos⟩
  obtain ⟨hmem, hnear⟩ := hy ε hεpos
  refine nearmax_in_ball (hbdS ε hεS) hmem hnear ?_
  linarith [hsupε, hεcube]

end

end PLaplacian
