/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.SeqExtract

/-!
# The filter-native characterisation of the half-relaxed limits

Below the upper limit the family is frequently above; frequent approach from
below bounds the upper limit; and dually for the lower limit, by transport
through negation.

These are what the contact-point argument needs, and they let it run along the
filter without ever extracting a sequence. That is a design choice worth
recording. The literature passes to sequences, because that is how analysts
write, and we built the machinery for it: the relaxed filter is countably
generated and admits sequences. But Mathlib's limit-superior API is
filter-native, and every sequential detour costs a diagonalisation against an
antitone basis. The formulation standard in the informal proofs is the harder
one to formalize, and the analyst habit of passing to sequences is a
hindrance here rather than a help.

## Main results

- frequently_lt_of_lt_ubar, le_ubar_of_frequently_le
- frequently_gt_of_lbar_lt
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The filter-native characterisation

The contact-point argument can run along the filter without ever extracting a
sequence. Both directions are available: below the upper limit the family is
frequently above, and frequent approach from below bounds the limit.

This is a design choice worth recording. The literature passes to sequences,
because that is how analysts write; but Mathlib's limit-superior API is
filter-native, and every sequential detour costs a diagonalisation against an
antitone basis. The formulation standard in the informal proofs is the harder
one to formalize.
-/

/-- **Below the upper limit, the family is frequently above.** -/
theorem frequently_lt_of_lt_ubar (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) (x : EuclSpace d) {a : ℝ}
    (ha : a < ubar u x) :
    ∃ᶠ q in relaxFilter x, a < u q.1 q.2 := by
  refine frequently_lt_of_lt_limsup ?_ ha
  exact (isBoundedUnder_ge_of_bound u hC x).isCobounded_flip

/-- **Frequent approach from below bounds the upper limit.** -/
theorem le_ubar_of_frequently_le (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) (x : EuclSpace d) {a : ℝ}
    (hfreq : ∃ᶠ q in relaxFilter x, a ≤ u q.1 q.2) :
    a ≤ ubar u x := by
  refine le_limsup_of_frequently_le hfreq ?_
  exact isBoundedUnder_le_of_bound u hC x

/-- The dual for the lower limit: above it, the family is frequently below. -/
theorem frequently_gt_of_lbar_lt (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) (x : EuclSpace d) {a : ℝ}
    (ha : lbar u x < a) :
    ∃ᶠ q in relaxFilter x, u q.1 q.2 < a := by
  have hneg : - a < ubar (fun ε y => - u ε y) x := by
    rw [lbar_eq_neg_ubar_neg] at ha
    linarith [ha]
  have hCneg : ∀ ε y, |(- u ε y)| ≤ C := by
    intro ε y
    rw [abs_neg]
    exact hC ε y
  have hfreq := frequently_lt_of_lt_ubar (fun ε y => - u ε y) hCneg x hneg
  exact hfreq.mono fun q hq => by linarith [hq]

end

end PLaplacian
