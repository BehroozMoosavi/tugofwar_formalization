/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.MinCmp

@[expose] public section

/-!
# The differential inequality at a minimum

The comparison at a minimum puts the operator applied to the test function
below the test function, and the expansion turns that into an upper bound of
zero on the quadratic term plus the error. In the limit the normalized
p-Laplacian is nonpositive, which is the supersolution condition.

The sign is the only difference from the maximum case, and the rearrangement
is again stated multiplied out, the division belonging with the limit passage.

## Main results

- diff_inequality_min
- normPLap_mul_le
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The differential inequality at a minimum

`dpp_comparison_local_min` gives `T_ε φ y ≤ φ y`; the expansion says
`T_ε φ y = φ y + ε²/(2(p+d)) Δ^N_p φ y + E`. Substituting and cancelling:

  `ε²/(2(p+d)) Δ^N_p φ y + E ≤ 0`,

which in the limit gives `Δ^N_p φ y ≤ 0`, the supersolution inequality.

The sign is the only difference from the maximum case, and the arithmetic
rearrangement is stated multiplied out for the same reason as there.
-/


/-- **The differential inequality at a minimum, at fixed `ε`.** -/
theorem diff_inequality_min [Nontrivial (EuclSpace d)] {p ε : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F u φ : EuclSpace d → ℝ}
    (hu : IsPHarmonious p ε Ω F u) (hφ : ContDiff ℝ 3 φ)
    (hφb : BddMeas φ) {y : EuclSpace d} (hy : y ∈ Ω)
    (hgrad : gradient φ y ≠ 0)
    (hge : ∀ w ∈ ball y ε, u y - φ y ≤ u w - φ w) :
    ∃ E : ℝ,
      ε ^ 2 / (2 * (p + (d : ℝ)))
          * normPLapOf p (gradient φ y) (fderiv ℝ (fderiv ℝ φ) y) + E
        ≤ 0 := by
  obtain ⟨E, hE⟩ := tugOfWarOp_expansion_final hd p hpd hφ hgrad hε
  refine ⟨E, ?_⟩
  have hcmp := dpp_comparison_local_min' hp hε hpd hu hφb hy hge
  rw [hE] at hcmp
  linarith [hcmp]

/-- The rearrangement, multiplied out. -/
theorem normPLap_mul_le {p ε : ℝ} (hpd : 0 < p + (d : ℝ)) (hε : 0 < ε)
    {I E : ℝ}
    (h : ε ^ 2 / (2 * (p + (d : ℝ))) * I + E ≤ 0) :
    ε ^ 2 * I ≤ - (2 * (p + (d : ℝ))) * E := by
  have h2 : (0:ℝ) < ε ^ 2 := by positivity
  have hpd2 : (0:ℝ) < 2 * (p + (d : ℝ)) := by linarith
  have hmul := mul_le_mul_of_nonneg_left h (le_of_lt hpd2)
  rw [mul_zero] at hmul
  have hexp : 2 * (p + (d : ℝ))
      * (ε ^ 2 / (2 * (p + (d : ℝ))) * I + E)
      = ε ^ 2 * I + 2 * (p + (d : ℝ)) * E := by
    field_simp
  rw [hexp] at hmul
  linarith [hmul]

end

end PLaplacian
