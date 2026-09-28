/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.KeyStep

/-!
# The differential inequality at fixed epsilon

The comparison through the operator gives the test function below its own
image; the expansion turns that into a statement about the normalized
p-Laplacian at order epsilon squared, with an error.

The rearrangement is stated multiplied out rather than divided by epsilon
squared. The division belongs with the passage to the limit, where the rate
makes the error vanish, and carrying it here would introduce side conditions
for nothing. That is the same separation of arithmetic from analysis used for
the core of the uniform convergence argument in the first layer and for the
deficit inequality in the third.

## Main results

- diff_inequality
- normPLap_mul_ge
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The differential inequality at fixed epsilon

`dpp_comparison` gives `φ y ≤ T_ε φ y`; the expansion turns that into

  `0 ≤ ε²/(2(p+d)) Δ^N_p φ y + E`.

The rearrangement is stated multiplied out rather than divided, since the
division by `ε²` belongs with the passage to the limit and carrying it here
would only introduce side conditions.
-/


/-- **The differential inequality at fixed `ε`.** -/
theorem diff_inequality [Nontrivial (EuclSpace d)] {p ε : ℝ} (hp : 2 ≤ p)
    (hd : 0 < d) (hε : 0 < ε) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F u φ : EuclSpace d → ℝ}
    (hu : IsPHarmonious p ε Ω F u) (hφ : ContDiff ℝ 3 φ)
    (hφb : BddMeas φ) {y : EuclSpace d} (hy : y ∈ Ω)
    (hgrad : gradient φ y ≠ 0) {c : ℝ}
    (hle : ∀ w, u w - φ w ≤ c) (heq : u y - φ y = c) :
    ∃ E : ℝ,
      0 ≤ ε ^ 2 / (2 * (p + (d : ℝ)))
          * normPLapOf p (gradient φ y) (fderiv ℝ (fderiv ℝ φ) y) + E := by
  obtain ⟨E, hE⟩ := tugOfWarOp_expansion_final hd p hpd hφ hgrad hε
  refine ⟨E, ?_⟩
  have hcmp := dpp_comparison hp hd hε hpd hu hφb hy hle heq
  rw [hE] at hcmp
  linarith [hcmp]

/-- **The rearrangement, multiplied out.** From the inequality at scale `ε`,
the negated error times the weight is at most the operator times `ε²`. -/
theorem normPLap_mul_ge {p ε : ℝ} (hpd : 0 < p + (d : ℝ)) (hε : 0 < ε)
    {I E : ℝ} (h : 0 ≤ ε ^ 2 / (2 * (p + (d : ℝ))) * I + E) :
    - (2 * (p + (d : ℝ))) * E ≤ ε ^ 2 * I := by
  have h2 : (0:ℝ) < ε ^ 2 := by positivity
  have hpd2 : (0:ℝ) < 2 * (p + (d : ℝ)) := by linarith
  have hne : (2 * (p + (d : ℝ))) ≠ 0 := ne_of_gt hpd2
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
