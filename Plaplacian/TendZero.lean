/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.ThreeRadii

/-!
# The quotient bound with an arbitrary multiple

The uniform bound is delivered in the form twice p plus d times a multiple,
and a statement of tending to zero wants an arbitrary positive bound. Since
the coefficient is positive and the multiple ranges over all positives, so
does the product, and the two forms agree.

## Main results

- exists_eta
- quotient_le_of_pos
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The quotient tends to zero

`FreqGen` consumes a `Tendsto` statement on the product filter.
`quotient_le_uniform` supplies a bound for every multiple within a radius
depending on the multiple alone, which is exactly the `ε-δ` form of tending
to zero --- but stated with the multiple as `2(p+d) η` rather than as an
arbitrary positive number.

Since `2(p+d) > 0` and `η` ranges over all positives, so does the product, so
the two forms agree. Making that explicit is the content here.
-/


/-- Every positive number is `2(p+d) η` for some positive `η`. -/
theorem exists_eta {p : ℝ} (hpd : 0 < p + (d : ℝ)) {c : ℝ} (hc : 0 < c) :
    ∃ η > 0, 2 * (p + (d : ℝ)) * η = c := by
  have hpd2 : (0:ℝ) < 2 * (p + (d : ℝ)) := by linarith
  refine ⟨c / (2 * (p + (d : ℝ))), by positivity, ?_⟩
  field_simp

/-- **The quotient bound, with an arbitrary multiple.**

For every `c > 0` there is a radius within which the quotient is below `c`. -/
theorem quotient_le_of_pos {p : ℝ} (hpd : 0 < p + (d : ℝ))
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x : EuclSpace d) {c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ w : EuclSpace d, ‖w‖ ≤ ε →
        |(2 * (p + (d : ℝ))) * taylorErr φ x w / ε ^ 2| ≤ c := by
  obtain ⟨η, hη, hηc⟩ := exists_eta (d := d) hpd hc
  obtain ⟨δ, hδ, hbd⟩ := quotient_le_uniform hpd hφ x hη
  refine ⟨δ, hδ, fun ε hε hεδ w hw => ?_⟩
  have h := hbd ε hε hεδ w hw
  rw [hηc] at h
  exact h

end

end PLaplacian
