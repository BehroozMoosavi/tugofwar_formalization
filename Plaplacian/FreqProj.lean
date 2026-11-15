/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.AsmFreq

@[expose] public section

/-!
# Projecting a frequency

The contact points arrive frequently along the product filter; the limit
argument wants a frequency in the parameter alone.

For a property of the first coordinate the projection is immediate: the
preimage of a member of the first factor is a member of the product. The
property actually at hand is not of that form --- the differential inequality
holds at the near-contact point, not at the base point --- so the dependence
on the second coordinate has to be removed first, by the continuity of the
operator away from the singular set. That removal, followed by this
projection, is the one outstanding step of the assembly.

## Main results

- frequently_fst_of_prod
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # Projecting a frequency

The contact points arrive frequently along the product filter; the limit
argument wants a frequency in the parameter alone. Projecting is the step
between.

If a property of the pair holds frequently on the product, and the property
depends only on the first coordinate, then it holds frequently on the first
factor. That is immediate: the preimage of a member of the first factor is a
member of the product.

The general case, where the property genuinely involves both coordinates, is
not immediate and is where the remaining step of the assembly has to do work:
the dependence on the second coordinate must be removed first, by continuity,
before the projection applies.
-/


/-- **Projection of a frequency, for a property of the first coordinate.** -/
theorem frequently_fst_of_prod {α β : Type*} {f : Filter α} {g : Filter β}
    [g.NeBot] {P : α → Prop}
    (h : ∃ᶠ q in f ×ˢ g, P q.1) :
    ∃ᶠ a in f, P a := by
  rw [Filter.frequently_iff] at h ⊢
  intro S hS
  obtain ⟨q, hq, hP⟩ := h (Filter.mem_prod_iff.2
    ⟨S, hS, Set.univ, Filter.univ_mem, by
      intro r hr
      exact hr.1⟩)
  exact ⟨q.1, hq, hP⟩

/-- The relaxed filter's second factor is not trivial, which the projection
needs. -/
instance nhds_neBot_euclSpace (x : EuclSpace d) : (nhds x).NeBot :=
  inferInstance

end

end PLaplacian
