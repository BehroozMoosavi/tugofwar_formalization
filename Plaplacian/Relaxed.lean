/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.OpBounded

/-!
# The half-relaxed limits

The upper and lower half-relaxed limits of a family of solutions, taken along
the product of the punctured right neighbourhood of zero with the
neighbourhood of the point.

A uniform bound on the family is what makes these finite, and it is a
hypothesis of every result here. Without it the limit superior of an unbounded
family is a junk value, the reals not being a complete lattice: the
completeness finding, recorded in the viscosity layer as a constraint that did
not bite there, binds here. The bound is available, since the existence
theorem bounds a solution by the bound on the initial datum with no dependence
on the parameter, so one datum serves the whole family.

## Main results

- relaxFilter, ubar, lbar
- lbar_le_ubar
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The half-relaxed limits

The filter is the product of the punctured neighbourhood of zero from the
right with the neighbourhood of the point, and the function sends a pair to
the value of the corresponding member of the family.

A uniform bound on the family is what makes these finite. Without it the
`limsup` of an unbounded family is a junk value, the reals not being a
complete lattice --- the completeness finding, predicted in the viscosity
layer, finally binding here. The bound is available:
`abs_iterLimit_le` bounds the solution by the bound on the initial datum,
with no dependence on the parameter, so feeding the same datum for every
parameter gives one constant for the whole family.
-/

/-- The filter along which the limits are taken. -/
def relaxFilter (x : EuclSpace d) : Filter (ℝ × EuclSpace d) :=
  (nhdsWithin (0 : ℝ) (Set.Ioi 0)) ×ˢ (nhds x)

/-- The upper half-relaxed limit. -/
def ubar (u : ℝ → EuclSpace d → ℝ) (x : EuclSpace d) : ℝ :=
  Filter.limsup (fun q : ℝ × EuclSpace d => u q.1 q.2) (relaxFilter x)

/-- The lower half-relaxed limit. -/
def lbar (u : ℝ → EuclSpace d → ℝ) (x : EuclSpace d) : ℝ :=
  Filter.liminf (fun q : ℝ × EuclSpace d => u q.1 q.2) (relaxFilter x)

/-- The filter is not trivial. -/
instance relaxFilter_neBot (x : EuclSpace d) : (relaxFilter x).NeBot := by
  unfold relaxFilter
  have h1 : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := by
    infer_instance
  exact Filter.prod_neBot.2 ⟨h1, inferInstance⟩

/-- A uniform bound gives boundedness above along the filter. -/
theorem isBoundedUnder_le_of_bound (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) (x : EuclSpace d) :
    Filter.IsBoundedUnder (· ≤ ·) (relaxFilter x)
      (fun q : ℝ × EuclSpace d => u q.1 q.2) := by
  refine Filter.isBoundedUnder_of ⟨C, fun q => ?_⟩
  exact le_of_abs_le (hC q.1 q.2)

/-- And below. -/
theorem isBoundedUnder_ge_of_bound (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) (x : EuclSpace d) :
    Filter.IsBoundedUnder (· ≥ ·) (relaxFilter x)
      (fun q : ℝ × EuclSpace d => u q.1 q.2) := by
  refine Filter.isBoundedUnder_of ⟨-C, fun q => ?_⟩
  have h := hC q.1 q.2
  have := abs_le.1 h
  exact this.1

/-- **The lower limit does not exceed the upper.** -/
theorem lbar_le_ubar (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) (x : EuclSpace d) :
    lbar u x ≤ ubar u x := by
  unfold lbar ubar
  exact Filter.liminf_le_limsup
    (isBoundedUnder_le_of_bound u hC x)
    (isBoundedUnder_ge_of_bound u hC x)

end

end PLaplacian
