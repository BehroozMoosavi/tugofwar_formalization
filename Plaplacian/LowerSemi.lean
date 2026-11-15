/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Semicont

@[expose] public section

/-!
# Semicontinuity of the lower half-relaxed limit

The dual, by transport through negation. Half the transport is available:
upperSemiContinuous_neg_iff connects the two semicontinuities. The other half
is not.

Mathlib has no lemma relating the limit inferior to the limit superior of the
negation, and the transport of the limit superior along an order isomorphism
does not apply, negation being order-reversing rather than an isomorphism. It
is proved here from the definitions: the defining set for the limit superior
of a negation is the negation of the defining set for the limit inferior, and
the infimum of a negated set is minus the supremum. That is elementary and
generally useful, so it is a candidate for upstreaming alongside the
monotonicity of the set average and the second-order necessary condition.

## Main results

- neg_set_eq, liminf_eq_neg_limsup_neg
- lbar_eq_neg_ubar_neg
- lowerSemicontinuous_lbar
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # Semicontinuity of the lower half-relaxed limit

The dual, by transport through negation: the lower limit of a family is minus
the upper limit of the negated family, and lower semicontinuity of a function
is upper semicontinuity of its negation.
-/


/-- The defining set for the limsup of a negation is the negation of the
defining set for the liminf. -/
theorem neg_set_eq {α : Type*} (u : α → ℝ) (F : Filter α) :
    {a : ℝ | ∀ᶠ x in F, - u x ≤ a} = - {a : ℝ | ∀ᶠ x in F, a ≤ u x} := by
  ext a
  simp only [Set.mem_ofPred_eq, Set.mem_neg]
  constructor
  · intro h
    filter_upwards [h] with x hx
    linarith [hx]
  · intro h
    filter_upwards [h] with x hx
    linarith [hx]

/-- **The limit inferior as minus the limit superior of the negation.** -/
theorem liminf_eq_neg_limsup_neg {α : Type*} (u : α → ℝ) (F : Filter α) :
    Filter.liminf u F = - Filter.limsup (fun x => - u x) F := by
  rw [Filter.liminf_eq, Filter.limsup_eq, neg_set_eq u F, Real.sInf_neg]
  ring


/-- The lower limit is minus the upper limit of the negation. -/
theorem lbar_eq_neg_ubar_neg (u : ℝ → EuclSpace d → ℝ) (x : EuclSpace d) :
    lbar u x = - ubar (fun ε y => - u ε y) x := by
  unfold lbar ubar
  exact liminf_eq_neg_limsup_neg (fun q : ℝ × EuclSpace d => u q.1 q.2)
    (relaxFilter x)

/-- **The lower limit is lower semicontinuous.** -/
theorem lowerSemicontinuous_lbar (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) :
    LowerSemicontinuous (lbar u) := by
  refine upperSemiContinuous_neg_iff.mp ?_
  have heq : (- lbar u)
      = ubar (fun ε y => - u ε y) := by
    funext y
    change - lbar u y = _
    rw [lbar_eq_neg_ubar_neg, neg_neg]
  rw [heq]
  refine upperSemicontinuous_ubar (fun ε y => - u ε y) (C := C) ?_
  intro ε y
  rw [abs_neg]
  exact hC ε y

end

end PLaplacian
