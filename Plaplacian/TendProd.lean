/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.TendZero

@[expose] public section

/-!
# The bound on the product filter

The quotient bound, stated for pairs whose point lies in the parameter's ball
about the base point. The ball condition is kept as a hypothesis on the pair
rather than folded into the filter, because that is what the near-contact
supplies and because the filter has no knowledge of the geometry.

## Main results

- Ioo_mem_nhdsWithin_Ioi'
- eventually_quotient_le
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The quotient as a Tendsto statement

`NormedAddGroup.tendsto_nhds_zero` turns tending to zero into: for every
positive bound, the norm is eventually below it. `quotient_le_of_pos` supplies
the bound within a radius, so what is needed is that the radius condition is
an eventual statement on the product filter.

It is: the set of parameters below the radius is a member of the punctured
right neighbourhood of zero, and the set of points within the parameter's ball
is handled by restricting attention to pairs where the point lies in the ball
--- which is where the argument's own geometry enters, since the near-contact
points do satisfy that.

This file proves the conversion with the ball membership as a hypothesis on
the pair, which is what the near-contact supplies.
-/


/-- The parameters below a radius form a member of the filter. -/
theorem Ioo_mem_nhdsWithin_Ioi' {δ : ℝ} (hδ : 0 < δ) :
    Set.Ioo (0:ℝ) δ ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) := by
  exact Ioo_mem_nhdsGT hδ

/-- **The eventual bound on the product filter**, for pairs whose point lies
in the parameter's ball about the base point. -/
theorem eventually_quotient_le {p : ℝ} (hpd : 0 < p + (d : ℝ))
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x : EuclSpace d) {c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, ∀ r : ℝ × EuclSpace d, r.1 ∈ Set.Ioo (0:ℝ) δ →
      ‖r.2 - x‖ ≤ r.1 →
        |(2 * (p + (d : ℝ))) * taylorErr φ x (r.2 - x) / r.1 ^ 2| ≤ c := by
  obtain ⟨δ, hδ, hbd⟩ := quotient_le_of_pos hpd hφ x hc
  refine ⟨δ, hδ, fun r hr hball => ?_⟩
  exact hbd r.1 hr.1 hr.2 (r.2 - x) hball

end

end PLaplacian
