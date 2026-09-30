/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.FilterChar

/-!
# The relaxed limit of a difference

For a continuous bounded test function, the upper relaxed limit of the
difference is the difference of the upper relaxed limit and the test function.
The second term contributes a genuine limit rather than a limit superior.

Mathlib has additivity of the limit superior only for a constant summand, so
continuity is used to replace the test function by its value at the point, up
to an arbitrary positive quantity, which is then sent to zero.

The boundedness the filter lemmas require needs no localisation: the
comparison through the operator already requires the test function bounded, so
the difference is bounded globally by the sum of the two bounds. We had
expected to need a localised statement and did not.

## Main results

- abs_sub_le_of_bounds
- eventually_sub_le
- ubar_sub_le
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The relaxed limit of a difference

`ubar (u - φ) x = ubar u x - φ x` for a continuous bounded `φ`. The second
term contributes a genuine limit, and Mathlib's additivity is for a constant
summand, so continuity is used to replace `φ` by the constant `φ x` up to
`η`, and `η` is then sent to zero.

One direction is given here; the other is symmetric.
-/


/-- The difference is globally bounded when both are. -/
theorem abs_sub_le_of_bounds (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {φ : EuclSpace d → ℝ} {B : ℝ}
    (hB : ∀ y, |φ y| ≤ B) :
    ∀ ε y, |u ε y - φ y| ≤ C + B := by
  intro ε y
  calc |u ε y - φ y| ≤ |u ε y| + |φ y| := abs_sub _ _
    _ ≤ C + B := by linarith [hC ε y, hB y]

/-- The difference is eventually below the shifted family. -/
theorem eventually_sub_le (u : ℝ → EuclSpace d → ℝ) {φ : EuclSpace d → ℝ}
    (hφ : Continuous φ) (x : EuclSpace d) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ q in relaxFilter x,
      u q.1 q.2 - φ q.2 ≤ u q.1 q.2 + (- φ x + η) := by
  -- continuity gives φ x - η < φ y near x
  have hcont : ∀ᶠ y in nhds x, φ x - η < φ y := by
    have h : Filter.Tendsto φ (nhds x) (nhds (φ x)) := hφ.continuousAt
    exact h.eventually (eventually_gt_nhds (by linarith : φ x - η < φ x))
  unfold relaxFilter
  rw [Filter.eventually_iff, Filter.mem_prod_iff]
  refine ⟨Set.univ, Filter.univ_mem, {y | φ x - η < φ y}, hcont, ?_⟩
  intro q hq
  have := hq.2
  simp only [Set.mem_ofPred_eq] at this
  simp only [Set.mem_ofPred_eq]
  linarith [this]

/-- **One direction: the relaxed limit of the difference is at most the
difference.** -/
theorem ubar_sub_le (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {φ : EuclSpace d → ℝ}
    (hφ : Continuous φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B) (x : EuclSpace d) :
    ubar (fun ε y => u ε y - φ y) x ≤ ubar u x - φ x := by
  refine le_of_forall_pos_le_add ?_
  intro η hη
  -- the eventual bound
  have hev := eventually_sub_le u hφ x hη
  -- transfer through the limsup
  have hmono : ubar (fun ε y => u ε y - φ y) x
      ≤ Filter.limsup (fun q : ℝ × EuclSpace d =>
          u q.1 q.2 + (- φ x + η)) (relaxFilter x) := by
    unfold ubar
    refine Filter.limsup_le_limsup hev ?_ ?_
    · exact (isBoundedUnder_ge_of_bound _
        (abs_sub_le_of_bounds u hC hB) x).isCobounded_flip
    · refine Filter.isBoundedUnder_of ⟨C + |(- φ x + η)|, fun q => ?_⟩
      have h1 := hC q.1 q.2
      have h2 := abs_le.1 h1
      have h3 := le_abs_self (- φ x + η)
      linarith [h2.2, h3]
  -- the constant comes out
  rw [limsup_add_const (relaxFilter x) _ (- φ x + η)
      (isBoundedUnder_le_of_bound u hC x)
      ((isBoundedUnder_ge_of_bound u hC x).isCobounded_flip)] at hmono
  unfold ubar at hmono ⊢
  linarith [hmono]

end

end PLaplacian
