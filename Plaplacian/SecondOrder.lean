/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib

@[expose] public section

/-!
# The second-order necessary condition

At an interior local maximum of a twice continuously differentiable function of
one real variable the second derivative is nonpositive, and dually at a
minimum.

This is absent from Mathlib. `Mathlib.Analysis.Calculus.LocalExtr.Basic` has
Fermat's theorem, `IsLocalMax.hasDerivAt_eq_zero`, together with the
tangent-cone refinements `IsLocalMaxOn.hasFDerivWithinAt_nonpos` and
`hasFDerivWithinAt_eq_zero`, but nothing of second order. Every consistency
proof in viscosity theory needs it, since the classical solution touching a
test function from below forces an inequality between Hessians.

The proof avoids Taylor's theorem. If the second derivative were positive at
the point, continuity would keep it positive on an interval, so the first
derivative would be strictly increasing there; being zero at the point by
Fermat, it would then be positive to the right, making the function strictly
increasing and contradicting the maximum. Each step is a application of
`strictMonoOn_of_deriv_pos`.

This is a candidate for upstreaming: the statement is elementary, general, and
belongs beside Fermat's theorem.

## Main results

- `IsLocalMax.deriv_deriv_nonpos`
- `IsLocalMin.deriv_deriv_nonneg`
-/

open Set Topology

/-!
# The second-order necessary condition

At an interior local maximum of a `C²` function of one real variable, the
second derivative is nonpositive. Mathlib has Fermat's theorem
(`IsLocalMax.hasDerivAt_eq_zero`) and the tangent-cone refinements in
`Mathlib.Analysis.Calculus.LocalExtr.Basic`, but nothing of second order.

The proof is by contradiction and avoids Taylor's theorem entirely. If
`g'' 0 > 0` then continuity of `g''` keeps it positive on an interval, so `g'`
is strictly increasing there; since `g' 0 = 0` by Fermat, `g' > 0` to the right
of `0`, so `g` is strictly increasing there, contradicting the maximum.
-/

/-- The second derivative of a `C²` function is continuous. -/
lemma continuous_deriv_deriv {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) :
    Continuous (deriv (deriv g)) := by
  have hd : Differentiable ℝ (deriv g) := hg.differentiable_deriv_two
  -- continuity of the second derivative from ContDiff 2
  have h1 : ContDiff ℝ 1 (deriv g) := ContDiff.deriv' hg
  exact h1.continuous_deriv le_rfl

/-- If the second derivative is positive at a point it is positive on an
interval around it. -/
lemma exists_interval_deriv_pos {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hpos : 0 < deriv (deriv g) 0) :
    ∃ δ > 0, ∀ t ∈ Ioo (-δ) δ, 0 < deriv (deriv g) t := by
  have hcont : ContinuousAt (deriv (deriv g)) 0 :=
    (continuous_deriv_deriv hg).continuousAt
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < deriv (deriv g) t :=
    hcont.eventually (eventually_gt_nhds hpos)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨ε, hε, fun t ht => ?_⟩
  refine hball ?_
  rw [Real.dist_eq, sub_zero, abs_lt]
  exact ⟨ht.1, ht.2⟩

/-- **The second-order necessary condition.** -/
theorem IsLocalMax.deriv_deriv_nonpos {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hmax : IsLocalMax g 0) : deriv (deriv g) 0 ≤ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨δ, hδ, hposδ⟩ := exists_interval_deriv_pos hg hcon
  -- `g'` is strictly increasing on the interval
  have hg1 : Differentiable ℝ (deriv g) := hg.differentiable_deriv_two
  have hmono : StrictMonoOn (deriv g) (Icc (-δ/2) (δ/2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (hg1.continuous.continuousOn) ?_
    intro t ht
    rw [interior_Icc] at ht
    exact hposδ t ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- Fermat: `g' 0 = 0`
  have h0 : deriv g 0 = 0 := hmax.deriv_eq_zero
  -- hence `g' > 0` on the right half
  have hpos' : ∀ t ∈ Ioc (0 : ℝ) (δ/2), 0 < deriv g t := by
    intro t ht
    have h1 : (0 : ℝ) ∈ Icc (-δ/2) (δ/2) := ⟨by linarith, by linarith⟩
    have h2 : t ∈ Icc (-δ/2) (δ/2) := ⟨by linarith [ht.1], ht.2⟩
    have := hmono h1 h2 ht.1
    rw [h0] at this
    exact this
  -- so `g` is strictly increasing on the right half
  have hgmono : StrictMonoOn g (Icc (0 : ℝ) (δ/2)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (hg.continuous.continuousOn) ?_
    intro t ht
    rw [interior_Icc] at ht
    exact hpos' t ⟨ht.1, le_of_lt ht.2⟩
  -- contradicting the local maximum
  have hmaxev : ∀ᶠ y in 𝓝 (0 : ℝ), g y ≤ g 0 := hmax
  obtain ⟨η, hη, hb⟩ := Metric.eventually_nhds_iff.1 hmaxev
  have hmaxη : ∀ y, |y - 0| < η → g y ≤ g 0 := by
    intro y hy
    exact hb (by rwa [Real.dist_eq])
  obtain ⟨s, hs1, hs2, hs3⟩ :
      ∃ s : ℝ, 0 < s ∧ s ≤ δ/2 ∧ s < η := by
    have hL : (δ/4 : ℝ) ≤ δ/2 := by linarith
    have hR : (η/2 : ℝ) < η := by linarith
    refine ⟨Min.min (δ/4 : ℝ) (η/2 : ℝ), ?_, ?_, ?_⟩
    · exact lt_min (by linarith : (0:ℝ) < δ/4) (by linarith : (0:ℝ) < η/2)
    · exact le_trans (min_le_left (δ/4 : ℝ) (η/2 : ℝ)) hL
    · exact lt_of_le_of_lt (min_le_right (δ/4 : ℝ) (η/2 : ℝ)) hR
  have hsIcc : s ∈ Icc (0 : ℝ) (δ/2) := ⟨le_of_lt hs1, hs2⟩
  have hsabs : |s - 0| < η := by
    rw [sub_zero, abs_of_pos hs1]
    exact hs3
  have hlt : g 0 < g s := hgmono ⟨le_rfl, by linarith⟩ hsIcc hs1
  exact absurd (hmaxη s hsabs) (not_le.2 hlt)

/-- The dual statement at a local minimum. -/
theorem IsLocalMin.deriv_deriv_nonneg {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hmin : IsLocalMin g 0) : 0 ≤ deriv (deriv g) 0 := by
  have hneg : IsLocalMax (fun t => -g t) 0 := hmin.neg
  have hgn : ContDiff ℝ 2 (fun t => -g t) := hg.neg
  have h := IsLocalMax.deriv_deriv_nonpos hgn hneg
  have hd1 : deriv (fun t => -g t) = fun t => -deriv g t := by
    funext t
    exact deriv.neg
  rw [hd1] at h
  have hd2 : deriv (fun t => -deriv g t) 0 = -deriv (deriv g) 0 := deriv.neg
  rw [hd2] at h
  linarith
