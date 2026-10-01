/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.QuotZero

/-!
# The error bound with the radii ordered

The multiple is given first, the radius comes from the C two estimate and
depends on the multiple alone, the parameter is then constrained below the
radius, and the increment by the parameter.

The order is visible in the statements: the radius is bound by an existential
appearing before the parameter and the increment are quantified, which is what
makes it uniform in them. Were it inside, the statement would be the pointwise
estimate restated and would carry no content. A reader can check that by eye
rather than by trusting the proof, which is the point of writing it this way.

## Main results

- taylorErr_le_uniform
- quotient_le_uniform
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The error bound with the radii ordered

Instantiating the arithmetic core's hypothesis. Three radii interact, and the
order is written into the statement so that a mismatch is a type error:

  `η` is given first;
  `δ` comes from the `C²` estimate and depends on `η` alone;
  `ε` is then constrained below `δ`;
  the increment `w` is constrained by `ε`.

The statement below is exactly that nesting. Note that `δ` is bound by an
existential appearing *before* `ε` and `w` are quantified, which is what makes
it uniform in them; were it inside, the statement would be the pointwise
estimate restated and would carry no content.
-/


/-- **The error bound, uniform in the parameter and the increment.**

For every `η > 0` there is `δ > 0` such that for every `ε` below `δ` and every
increment of norm at most `ε`, the Taylor error is at most `η ε²`. -/
theorem taylorErr_le_uniform {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x : EuclSpace d) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ w : EuclSpace d, ‖w‖ ≤ ε → |taylorErr φ x w| ≤ η * ε ^ 2 := by
  obtain ⟨δ, hδ, hbd⟩ := exists_taylorErr_le hφ x hη
  refine ⟨δ, hδ, fun ε hε hεδ w hw => ?_⟩
  -- the increment is below the radius
  have hwδ : ‖w‖ < δ := lt_of_le_of_lt hw hεδ
  have h1 := hbd w hwδ
  -- and its square is below the parameter's
  have hw2 : ‖w‖ ^ 2 ≤ ε ^ 2 := by
    have h0 : (0:ℝ) ≤ ‖w‖ := norm_nonneg w
    nlinarith [hw, h0, hε]
  nlinarith [h1, hw2, hη.le, sq_nonneg ‖w‖]

/-- **The quotient bound, with the radii ordered.**

Combining with the arithmetic core: for every `η` there is a radius within
which the quotient is below `2(p+d) η`. -/
theorem quotient_le_uniform {p : ℝ} (hpd : 0 < p + (d : ℝ))
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x : EuclSpace d) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ ε : ℝ, 0 < ε → ε < δ →
      ∀ w : EuclSpace d, ‖w‖ ≤ ε →
        |(2 * (p + (d : ℝ))) * taylorErr φ x w / ε ^ 2|
          ≤ 2 * (p + (d : ℝ)) * η := by
  obtain ⟨δ, hδ, hbd⟩ := taylorErr_le_uniform hφ x hη
  refine ⟨δ, hδ, fun ε hε hεδ w hw => ?_⟩
  exact quotient_le_of_bound (E := fun _ => taylorErr φ x w) hpd hε
    (hbd ε hε hεδ w hw)

end

end PLaplacian
