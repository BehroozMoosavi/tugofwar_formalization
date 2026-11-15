/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.UbarSub

@[expose] public section

/-!
# The relaxed limit of a difference

The reverse inequality, by the same argument with the roles exchanged, and the
equality by antisymmetry: the upper relaxed limit of the difference of a family
and a continuous bounded test function is the difference of the upper relaxed
limit and the test function.

This is what the contact-point argument needs. A maximum of the relaxed limit
minus the test function is a maximum of the relaxed limit of the difference,
and the filter characterisation then applies to the latter.

## Main results

- eventually_le_sub, le_ubar_sub
- ubar_sub
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The reverse direction

`ubar u x - φ x ≤ ubar (u - φ) x`, by the same argument with the roles
exchanged: near `x` the test function is below `φ x + η`, so the family is
below the difference plus that constant, and `η` goes to zero.
-/

/-- Near the point the test function exceeds its value less `η`, so the
family is eventually above the difference less the constant. -/
theorem eventually_le_sub (u : ℝ → EuclSpace d → ℝ) {φ : EuclSpace d → ℝ}
    (hφ : Continuous φ) (x : EuclSpace d) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ q in relaxFilter x,
      u q.1 q.2 + (- φ x - η) ≤ u q.1 q.2 - φ q.2 := by
  have hcont : ∀ᶠ y in nhds x, φ y < φ x + η := by
    have h : Filter.Tendsto φ (nhds x) (nhds (φ x)) := hφ.continuousAt
    exact h.eventually (eventually_lt_nhds (by linarith : φ x < φ x + η))
  unfold relaxFilter
  rw [Filter.eventually_iff, Filter.mem_prod_iff]
  refine ⟨Set.univ, Filter.univ_mem, {y | φ y < φ x + η}, hcont, ?_⟩
  intro q hq
  have h2 := hq.2
  simp only [Set.mem_ofPred_eq] at h2
  simp only [Set.mem_ofPred_eq]
  linarith [h2]

/-- **The reverse direction.** -/
theorem le_ubar_sub (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {φ : EuclSpace d → ℝ}
    (hφ : Continuous φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B) (x : EuclSpace d) :
    ubar u x - φ x ≤ ubar (fun ε y => u ε y - φ y) x := by
  refine le_of_forall_pos_le_add ?_
  intro η hη
  have hev := eventually_le_sub u hφ x hη
  have hmono : Filter.limsup (fun q : ℝ × EuclSpace d =>
        u q.1 q.2 + (- φ x - η)) (relaxFilter x)
      ≤ ubar (fun ε y => u ε y - φ y) x := by
    unfold ubar
    refine Filter.limsup_le_limsup hev ?_ ?_
    · have hb : Filter.IsBoundedUnder (· ≥ ·) (relaxFilter x)
          (fun q : ℝ × EuclSpace d => u q.1 q.2 + (- φ x - η)) := by
        refine Filter.isBoundedUnder_of ⟨- C + (- φ x - η), fun q => ?_⟩
        have h1 := abs_le.1 (hC q.1 q.2)
        linarith [h1.1]
      exact hb.isCobounded_flip
    · exact isBoundedUnder_le_of_bound _
        (abs_sub_le_of_bounds u hC hB) x
  rw [limsup_add_const (relaxFilter x) _ (- φ x - η)
      (isBoundedUnder_le_of_bound u hC x)
      ((isBoundedUnder_ge_of_bound u hC x).isCobounded_flip)] at hmono
  unfold ubar at hmono ⊢
  linarith [hmono]

/-- **The relaxed limit of a difference.** -/
theorem ubar_sub (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {φ : EuclSpace d → ℝ}
    (hφ : Continuous φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B) (x : EuclSpace d) :
    ubar (fun ε y => u ε y - φ y) x = ubar u x - φ x :=
  le_antisymm (ubar_sub_le u hC hφ hB x) (le_ubar_sub u hC hφ hB x)

end

end PLaplacian
