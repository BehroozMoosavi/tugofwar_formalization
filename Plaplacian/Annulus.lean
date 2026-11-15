/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Strict

@[expose] public section

/-!
# The gap on the annulus

On the annulus between two radii about the base point, the relaxed difference
lies a fixed positive amount below its value at the strict maximum. The
relaxed difference is upper semicontinuous and the annulus compact, so the
maximum over the annulus is attained, and it is strictly below the strict
maximum because no point of the annulus is the base point.

This is the first step of a route to the convergence of the near-maximizers
that avoids extracting a sequence. The standard argument passes to a
subsequence; here the gap on the annulus is combined with compactness to give
a uniform eventual bound, and the near-maximizers, having values above that
bound, are excluded from the annulus. That keeps the argument filter-native,
which is the grain of the library, and avoids the diagonalisation the
sequential form would need.

Mathlib has no subtraction lemma for upper semicontinuity, so the relaxed
difference is written as the upper limit plus the negated test function.

## Main results

- annulus, isCompact_annulus, ne_of_mem_annulus
- usc_ubar_sub
- annulus_gap
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The gap on the annulus

On the annulus `A = closedBall x₀ r \ ball x₀ ρ`, the relaxed difference is
strictly below its value at the strict maximum. Since the relaxed difference is
upper semicontinuous and `A` is compact, it attains a maximum on `A`, which is
below the strict maximum's value because no point of `A` is the base point.

This probe finds the attainment lemma for upper semicontinuous functions.
-/


/-- The annulus. -/
def annulus (x₀ : EuclSpace d) (ρ r : ℝ) : Set (EuclSpace d) :=
  closedBall x₀ r \ ball x₀ ρ

/-- It is compact, being closed in a compact set. -/
theorem isCompact_annulus (x₀ : EuclSpace d) (ρ r : ℝ) :
    IsCompact (annulus x₀ ρ r) := by
  unfold annulus
  exact (isCompact_closedBall x₀ r).diff isOpen_ball

/-- No point of the annulus is the base point, for positive inner radius. -/
theorem ne_of_mem_annulus {x₀ w : EuclSpace d} {ρ r : ℝ} (hρ : 0 < ρ)
    (hw : w ∈ annulus x₀ ρ r) : w ≠ x₀ := by
  intro h
  rw [h] at hw
  exact hw.2 (mem_ball_self hρ)


/-- The relaxed difference is upper semicontinuous: the upper limit is, and
subtracting a continuous function preserves it. Mathlib has no `sub` for upper
semicontinuity, so it is written as adding the negation. -/
theorem usc_ubar_sub (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {φ : EuclSpace d → ℝ} (hφ : Continuous φ) :
    UpperSemicontinuous (fun w => ubar u w - φ w) := by
  have h1 : UpperSemicontinuous (ubar u) := upperSemicontinuous_ubar u hC
  have h2 : UpperSemicontinuous (fun w => -φ w) :=
    (hφ.neg).upperSemicontinuous
  have h := h1.add h2
  simpa [sub_eq_add_neg] using h

/-- **The gap on the annulus.** At a strict maximum, the relaxed difference is
bounded below the maximum's value by a fixed positive amount throughout the
annulus. -/
theorem annulus_gap (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {φ : EuclSpace d → ℝ} (hφ : Continuous φ)
    {x₀ : EuclSpace d} {ρ r : ℝ} (hρ : 0 < ρ)
    (hstrict : IsStrictMaxOn (fun w => ubar u w - φ w) x₀ r) :
    ∃ η > 0, ∀ w ∈ annulus x₀ ρ r,
      ubar u w - φ w ≤ (ubar u x₀ - φ x₀) - η := by
  by_cases hne : (annulus x₀ ρ r).Nonempty
  · -- the maximum on the annulus is attained
    have husc : UpperSemicontinuousOn (fun w => ubar u w - φ w)
        (annulus x₀ ρ r) := (usc_ubar_sub u hC hφ).upperSemicontinuousOn _
    obtain ⟨a, ha, hmax⟩ := husc.exists_isMaxOn hne (isCompact_annulus x₀ ρ r)
    -- and it is strictly below the strict maximum
    have hlt : ubar u a - φ a < ubar u x₀ - φ x₀ :=
      hstrict a ha.1 (ne_of_mem_annulus hρ ha)
    refine ⟨(ubar u x₀ - φ x₀) - (ubar u a - φ a), by linarith [hlt],
      fun w hw => ?_⟩
    have h3 : ubar u w - φ w ≤ ubar u a - φ a := hmax hw
    linarith [h3]
  · -- an empty annulus makes the bound vacuous
    refine ⟨1, one_pos, fun w hw => ?_⟩
    exact absurd ⟨w, hw⟩ hne

end

end PLaplacian
