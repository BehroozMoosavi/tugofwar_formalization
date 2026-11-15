/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.LimitPassage

@[expose] public section

/-!
# Semicontinuity of the upper half-relaxed limit

The upper half-relaxed limit is upper semicontinuous, which is the first field
of the subsolution predicate.

Two steps need care beyond the standard argument. The bound at nearby points
comes out non-strict while semicontinuity wants it strict, so an intermediate
value is interposed. And the witnessing neighbourhood must be shrunk to an
open subset: that a point belongs to a neighbourhood of another point does not
make it a neighbourhood of the first, and only openness gives that. Our first
attempt asserted the latter directly, which is false, and is the kind of step
that reads as obvious and is not.

## Main results

- eventually_lt_of_ubar_lt, exists_prod_nhds_of_ubar_lt
- ubar_le_of_bound
- upperSemicontinuous_ubar
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # Semicontinuity of the upper half-relaxed limit

The bound is unpacked into a product neighbourhood, and an intermediate value
converts the resulting non-strict bound at nearby points into the strict one
semicontinuity requires.
-/

/-- The family is eventually below any bound exceeding the upper limit. -/
theorem eventually_lt_of_ubar_lt (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) (x : EuclSpace d) {a : ℝ}
    (ha : ubar u x < a) :
    ∀ᶠ q in relaxFilter x, u q.1 q.2 < a := by
  refine eventually_lt_of_limsup_lt ha ?_
  exact isBoundedUnder_le_of_bound u hC x

/-- The eventual bound as a product neighbourhood. -/
theorem exists_prod_nhds_of_ubar_lt (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) (x : EuclSpace d) {a : ℝ}
    (ha : ubar u x < a) :
    ∃ S ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0), ∃ V ∈ nhds x,
      ∀ ε ∈ S, ∀ y ∈ V, u ε y < a := by
  have hev := eventually_lt_of_ubar_lt u hC x ha
  unfold relaxFilter at hev
  rw [Filter.eventually_iff, Filter.mem_prod_iff] at hev
  obtain ⟨S, hS, V, hV, hsub⟩ := hev
  refine ⟨S, hS, V, hV, fun ε hεS y hyV => ?_⟩
  exact hsub (Set.mk_mem_prod hεS hyV)

/-- At a point of the witnessing neighbourhood the upper limit is bounded. -/
theorem ubar_le_of_bound (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {S : Set ℝ}
    (hS : S ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0)) {V : Set (EuclSpace d)}
    {b : ℝ} (hbd : ∀ ε ∈ S, ∀ y ∈ V, u ε y ≤ b)
    {y : EuclSpace d} (hyV : V ∈ nhds y) :
    ubar u y ≤ b := by
  unfold ubar
  refine Filter.limsup_le_of_le ?_ ?_
  · exact (isBoundedUnder_ge_of_bound u hC y).isCobounded_flip
  · rw [Filter.eventually_iff]
    unfold relaxFilter
    rw [Filter.mem_prod_iff]
    refine ⟨S, hS, V, hyV, ?_⟩
    intro q hq
    exact hbd q.1 hq.1 q.2 hq.2

/-- **The upper limit is upper semicontinuous.** -/
theorem upperSemicontinuous_ubar (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) :
    UpperSemicontinuous (ubar u) := by
  intro x a ha
  -- an intermediate value
  obtain ⟨b, hb1, hb2⟩ := exists_between ha
  obtain ⟨S, hS, V, hV, hbd⟩ := exists_prod_nhds_of_ubar_lt u hC x hb1
  -- shrink to an open subset, which is a neighbourhood of each of its points
  obtain ⟨W, hWV, hWopen, hxW⟩ := _root_.mem_nhds_iff.1 hV
  filter_upwards [hWopen.mem_nhds hxW] with y hyW
  have hWy : W ∈ nhds y := hWopen.mem_nhds hyW
  have hle : ubar u y ≤ b :=
    ubar_le_of_bound u hC hS
      (fun ε hεS w hwW => le_of_lt (hbd ε hεS w (hWV hwW))) hWy
  linarith [hle, hb2]

end

end PLaplacian
