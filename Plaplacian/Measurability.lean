/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Plaplacian.Domain

@[expose] public section

/-!
# Measurability of the extreme values over a ball

For the step operator to act on bounded *measurable* functions, the maps
`x ↦ sup_{B ε x} v` and `x ↦ inf_{B ε x} v` must be measurable. This file
proves that, and the proof explains a design constraint on the operator.

## Why the balls must be open

Over an **open** ball the argument is immediate: the superlevel set is a union
of balls,

  `{x | λ < sup_{B ε x} v} = ⋃ {y | λ < v y}, ball y ε`,

hence open, hence measurable.

Over a **closed** ball this fails. Luiro–Parviainen–Saksman (*On the existence
and uniqueness of p-harmonious functions*, Differential Integral Equations 27
(2014), Example 2.4) construct a bounded Borel `u : ℝ³ → ℝ` for which
`x ↦ sup_{closedBall x 1} u` is not Borel, by taking the indicator of a Borel
set whose projection is non-Borel and wrapping it onto a cylinder. So the
supremum over closed balls does not preserve Borel measurability, and the
class of bounded measurable functions would not be invariant under a
closed-ball operator.

This is why `tugOfWarOp` averages the extreme values over `ball x ε` rather
than `closedBall x ε`. Note the boundary strip still uses `≤`, matching
`Γ_ε = {x ∉ Ω : dist x Ω ≤ ε}` in the same reference.

## Main results

- `sSup_ball_gt_iff`, `sInf_ball_lt_iff`: pointwise characterisation of the
  strict superlevel and sublevel conditions.
- `isOpen_sSup_ball_gt`, `isOpen_sInf_ball_lt`: those sets are open.
- `measurable_sSup_ball`, `measurable_sInf_ball`: **the extreme values are
  measurable.**
-/

open MeasureTheory Metric Set

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-! ### Pointwise characterisation -/

/-- `sup_{B ε x} v > λ` exactly when some point of the ball has `v y > λ`. -/
theorem sSup_ball_gt_iff (v : EuclSpace d → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hb : ∃ C, ∀ y, |v y| ≤ C) (lam : ℝ) (x : EuclSpace d) :
    lam < sSup (v '' ball x ε) ↔ ∃ y ∈ ball x ε, lam < v y := by
  obtain ⟨C, hC⟩ := hb
  have hne : (v '' ball x ε).Nonempty := ⟨v x, x, mem_ball_self hε, rfl⟩
  have hbdd : BddAbove (v '' ball x ε) :=
    ⟨C, by rintro a ⟨y, -, rfl⟩; exact (abs_le.1 (hC y)).2⟩
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    exact absurd (csSup_le hne (by rintro a ⟨y, hy, rfl⟩; exact hcon y hy))
      (not_le.2 h)
  · rintro ⟨y, hy, hlt⟩
    exact lt_of_lt_of_le hlt (le_csSup hbdd ⟨y, hy, rfl⟩)

/-- `inf_{B ε x} v < λ` exactly when some point of the ball has `v y < λ`. -/
theorem sInf_ball_lt_iff (v : EuclSpace d → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hb : ∃ C, ∀ y, |v y| ≤ C) (lam : ℝ) (x : EuclSpace d) :
    sInf (v '' ball x ε) < lam ↔ ∃ y ∈ ball x ε, v y < lam := by
  obtain ⟨C, hC⟩ := hb
  have hne : (v '' ball x ε).Nonempty := ⟨v x, x, mem_ball_self hε, rfl⟩
  have hbdd : BddBelow (v '' ball x ε) :=
    ⟨-C, by rintro a ⟨y, -, rfl⟩; exact (abs_le.1 (hC y)).1⟩
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    exact absurd (le_csInf hne (by rintro a ⟨y, hy, rfl⟩; exact hcon y hy))
      (not_le.2 h)
  · rintro ⟨y, hy, hlt⟩
    exact lt_of_le_of_lt (csInf_le hbdd ⟨y, hy, rfl⟩) hlt

/-! ### Openness of the level sets -/

theorem isOpen_sSup_ball_gt (v : EuclSpace d → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hb : ∃ C, ∀ y, |v y| ≤ C) (lam : ℝ) :
    IsOpen {x : EuclSpace d | lam < sSup (v '' ball x ε)} := by
  have hset : {x : EuclSpace d | lam < sSup (v '' ball x ε)}
      = ⋃ y ∈ {y : EuclSpace d | lam < v y}, ball y ε := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_iUnion, exists_prop]
    rw [sSup_ball_gt_iff v hε hb lam x]
    exact ⟨fun ⟨y, hy, h⟩ => ⟨y, h, by rw [mem_ball] at hy ⊢; rwa [dist_comm]⟩,
           fun ⟨y, h, hy⟩ => ⟨y, by rw [mem_ball] at hy ⊢; rwa [dist_comm], h⟩⟩
  rw [hset]
  exact isOpen_biUnion fun y _ => isOpen_ball

theorem isOpen_sInf_ball_lt (v : EuclSpace d → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hb : ∃ C, ∀ y, |v y| ≤ C) (lam : ℝ) :
    IsOpen {x : EuclSpace d | sInf (v '' ball x ε) < lam} := by
  have hset : {x : EuclSpace d | sInf (v '' ball x ε) < lam}
      = ⋃ y ∈ {y : EuclSpace d | v y < lam}, ball y ε := by
    ext x
    simp only [Set.mem_ofPred_eq, mem_iUnion, exists_prop]
    rw [sInf_ball_lt_iff v hε hb lam x]
    exact ⟨fun ⟨y, hy, h⟩ => ⟨y, h, by rw [mem_ball] at hy ⊢; rwa [dist_comm]⟩,
           fun ⟨y, h, hy⟩ => ⟨y, by rw [mem_ball] at hy ⊢; rwa [dist_comm], h⟩⟩
  rw [hset]
  exact isOpen_biUnion fun y _ => isOpen_ball

/-! ### Measurability -/

/-- **The supremum over open balls is measurable.** -/
theorem measurable_sSup_ball (v : EuclSpace d → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hb : ∃ C, ∀ y, |v y| ≤ C) :
    Measurable (fun x : EuclSpace d => sSup (v '' ball x ε)) :=
  measurable_of_Ioi fun lam => (isOpen_sSup_ball_gt v hε hb lam).measurableSet

/-- **The infimum over open balls is measurable.** -/
theorem measurable_sInf_ball (v : EuclSpace d → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hb : ∃ C, ∀ y, |v y| ≤ C) :
    Measurable (fun x : EuclSpace d => sInf (v '' ball x ε)) :=
  measurable_of_Iio fun lam => (isOpen_sInf_ball_lt v hε hb lam).measurableSet

/-! ### The difference estimates

These drive the comparison proof: the difference of suprema is controlled by
the supremum of the difference, and likewise for infima. Summing the two with
weights `α/2` gives the factor `α` in the key estimate.
-/

/-- `sup v - sup u ≤ sup (v - u)`. -/
theorem sSup_sub_sSup_le (u v : EuclSpace d → ℝ) (s : Set (EuclSpace d))
    (hs : s.Nonempty) (hu : BddAbove (u '' s))
    (hd : BddAbove ((fun y => v y - u y) '' s)) :
    sSup (v '' s) - sSup (u '' s) ≤ sSup ((fun y => v y - u y) '' s) := by
  rw [sub_le_iff_le_add]
  refine csSup_le (hs.image v) ?_
  rintro a ⟨y, hy, rfl⟩
  have h1 : v y - u y ≤ sSup ((fun y => v y - u y) '' s) :=
    le_csSup hd ⟨y, hy, rfl⟩
  have h2 : u y ≤ sSup (u '' s) := le_csSup hu ⟨y, hy, rfl⟩
  linarith

/-- `inf v - inf u ≤ sup (v - u)`. -/
theorem sInf_sub_sInf_le (u v : EuclSpace d → ℝ) (s : Set (EuclSpace d))
    (hs : s.Nonempty) (hv : BddBelow (v '' s))
    (hd : BddAbove ((fun y => v y - u y) '' s)) :
    sInf (v '' s) - sInf (u '' s) ≤ sSup ((fun y => v y - u y) '' s) := by
  rw [sub_le_iff_le_add, ← sub_le_iff_le_add']
  refine le_csInf (hs.image u) ?_
  rintro a ⟨y, hy, rfl⟩
  have h1 : v y - u y ≤ sSup ((fun y => v y - u y) '' s) :=
    le_csSup hd ⟨y, hy, rfl⟩
  have h2 : sInf (v '' s) ≤ v y := csInf_le hv ⟨y, hy, rfl⟩
  linarith

end PLaplacian
