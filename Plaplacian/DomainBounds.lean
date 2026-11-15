/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Plaplacian.DeficitMono

@[expose] public section

/-!
# Containment and boundedness of the epsilon-closure

Three facts about `closureEps` needed to instantiate the uniform convergence
argument.

The first is a correction. One might expect the deficit supremum in the
chained estimate of Luiro-Parviainen-Saksman to be taken over the domain, but
the supremum appearing in the estimate is over a ball centred at a point of the
domain, and such a ball reaches into the boundary strip. The supremum must
therefore be taken over `closureEps`, not over the domain, and
`ball_subset_closureEps` is what licenses that. This is visible in the informal
proof only if one reads the ranges of the suprema carefully.

The second and third supply nonemptiness and boundedness of `closureEps`, the
latter giving finite measure and hence the dominated convergence hypothesis of
`tendsto_setIntegral_deficit`. Boundedness needs a little care: mathlib's
`Bornology.IsBounded.subset` goes the wrong way, and there is no
`isBounded_thickening`, so the bound is obtained by extracting a nearby point
of the domain from the `infDist` hypothesis via the contrapositive of
`Metric.le_infDist`.

## Main results

- `ball_subset_closureEps`
- `closureEps_nonempty`
- `exists_dist_lt`, `norm_le_of_infDist_le`, `isBounded_closureEps`
-/

open MeasureTheory Metric Set Filter

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-- The open ball at a point of the domain lies in the epsilon-closure. This is
why the deficit supremum must range over `closureEps`. -/
theorem ball_subset_closureEps (Ω : Set (EuclSpace d)) {ε : ℝ}
    {x : EuclSpace d} (hx : x ∈ Ω) :
    ball x ε ⊆ closureEps Ω ε :=
  fun _ hy => closedBall_subset_union Ω hx (ball_subset_closedBall hy)

theorem closureEps_nonempty {Ω : Set (EuclSpace d)} (hΩ : Ω.Nonempty)
    (ε : ℝ) : (closureEps Ω ε).Nonempty :=
  hΩ.mono (subset_closureEps Ω ε)

/-- From `infDist y Ω < r`, extract a point of `Ω` within `r` of `y`. Proved by
contradiction from `Metric.le_infDist`, since mathlib has no direct form. -/
theorem exists_dist_lt {Ω : Set (EuclSpace d)} (hΩ : Ω.Nonempty)
    {y : EuclSpace d} {r : ℝ} (h : Metric.infDist y Ω < r) :
    ∃ z ∈ Ω, dist y z < r := by
  by_contra hcon
  push Not at hcon
  have : r ≤ Metric.infDist y Ω :=
    (Metric.le_infDist hΩ).2 fun z hz => hcon z hz
  linarith

/-- A point of the strip has norm controlled by a bound on the domain. -/
theorem norm_le_of_infDist_le {Ω : Set (EuclSpace d)} (hΩ : Ω.Nonempty)
    {R : ℝ} (hR : ∀ z ∈ Ω, ‖z‖ ≤ R)
    {ε : ℝ} {y : EuclSpace d} (hy : Metric.infDist y Ω ≤ ε) :
    ‖y‖ ≤ R + ε + 1 := by
  obtain ⟨z, hzΩ, hz⟩ := exists_dist_lt hΩ (show Metric.infDist y Ω < ε + 1 by
    linarith)
  have h1 : ‖z‖ ≤ R := hR z hzΩ
  have h2 : ‖y‖ ≤ ‖z‖ + dist y z := by
    rw [dist_eq_norm]
    have hyz : y = z + (y - z) := by abel
    calc ‖y‖ = ‖z + (y - z)‖ := by rw [← hyz]
      _ ≤ ‖z‖ + ‖y - z‖ := norm_add_le _ _
  linarith

/-- **The epsilon-closure of a bounded set is bounded**, hence of finite
measure. This supplies the dominated convergence hypothesis. -/
theorem isBounded_closureEps {Ω : Set (EuclSpace d)} (hΩ : Ω.Nonempty)
    (hb : Bornology.IsBounded Ω) {ε : ℝ} (hε : 0 ≤ ε) :
    Bornology.IsBounded (closureEps Ω ε) := by
  obtain ⟨R, hR⟩ := hb.subset_closedBall 0
  have hRnorm : ∀ z ∈ Ω, ‖z‖ ≤ R := by
    intro z hz
    have := hR hz
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  refine Bornology.IsBounded.subset
    (Metric.isBounded_closedBall (x := (0 : EuclSpace d)) (r := R + ε + 1)) ?_
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  rcases hy with hyΩ | hyΓ
  · have := hRnorm y hyΩ
    linarith
  · exact norm_le_of_infDist_le hΩ hRnorm hyΓ.2

end PLaplacian

end
