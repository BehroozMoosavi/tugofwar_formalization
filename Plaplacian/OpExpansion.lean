/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Combine

/-!
# The asymptotic expansion of the step operator

The step operator applied to a test function equals the value at the point,
plus epsilon squared over twice p plus d times the normalized p-Laplacian,
plus a weighted error. This is the theorem the asymptotic layer exists to
produce.

The two halves are carried as hypotheses rather than substituted inline, which
verifies the weight arithmetic independently of the error bookkeeping, as was
done for the arithmetic core of the uniform convergence argument in Layer 1.
The average hypothesis is discharged directly by setAverage_expansion. The
extreme-value hypothesis follows from the sandwich of
Plaplacian.ExtremeExpansion, once the two-sided inequality there is converted
into an equality with an error term.

The bracket appearing in the expansion is the operator normPLapOf of
Plaplacian.Operator, defined from the partial differential equation rather
than chosen to make this come out. That the asymptotics independently produce
the same combination, with the same constant, is a check on both.

## Main results

- tugOfWarOp_eq
- tugOfWarOp_expansion
- tugOfWarOp_expansion_normPLap
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The asymptotic expansion of the step operator

The operator is

  `T_ε φ x = (p-2)/(p+d)/2 * (sSup + sInf) + (d+2)/(p+d) * ⨍`.

The extreme values are over open balls; `sSup_ball_eq_closedBall` converts
them to closed ones, where the expansion was proved. The average is expanded
by `setAverage_expansion`, and `combine_weights` with
`bracket_eq_normPLap` assembles the result.

The statement below carries the extreme-value terms abstractly, as `S` for
the average of the supremum and infimum, so that the arithmetic is verified
independently of the error bookkeeping. Substituting the sandwich of
`Plaplacian.ExtremeExpansion` for `S` gives the expansion with explicit
errors.
-/

/-- The operator, with the extreme-value average and the ball average named. -/
theorem tugOfWarOp_eq (p ε : ℝ) (v : EuclSpace d → ℝ) (x : EuclSpace d) :
    tugOfWarOp p ε v x
      = (p - 2) / (p + (d : ℝ))
          * ((sSup (v '' ball x ε) + sInf (v '' ball x ε)) / 2)
        + ((d : ℝ) + 2) / (p + (d : ℝ)) * ⨍ y in ball x ε, v y := by
  unfold tugOfWarOp
  ring

/-- **The asymptotic expansion, with the two halves supplied.**

If the average of the extreme values expands with infinity-Laplacian term `I`
and error `e₁`, and the ball average with Laplacian term `L` and error `e₂`,
then the operator expands with the normalized `p`-Laplacian and the weighted
error. -/
theorem tugOfWarOp_expansion (p : ℝ) (hpd : 0 < p + (d : ℝ)) (ε : ℝ)
    (φ : EuclSpace d → ℝ) (x : EuclSpace d) {I L e₁ e₂ : ℝ}
    (hS : (sSup (φ '' ball x ε) + sInf (φ '' ball x ε)) / 2
        = φ x + (ε ^ 2 / 2) * I + e₁)
    (hA : (⨍ y in ball x ε, φ y)
        = φ x + ε ^ 2 / (2 * ((d : ℝ) + 2)) * L + e₂) :
    tugOfWarOp p ε φ x
      = φ x + ε ^ 2 / (2 * (p + (d : ℝ))) * ((p - 2) * I + L)
        + ((p - 2) / (p + (d : ℝ)) * e₁
            + ((d : ℝ) + 2) / (p + (d : ℝ)) * e₂) := by
  rw [tugOfWarOp_eq, hS, hA]
  have hw := combine_weights (d := d) p hpd ε I L
  have hab := alpha_add_beta (d := d) p hpd
  linear_combination hw + (φ x) * hab

/-- **And the bracket is the normalized `p`-Laplacian**, so the expansion
reads with the operator of `Plaplacian.Operator`. -/
theorem tugOfWarOp_expansion_normPLap (p : ℝ) (hpd : 0 < p + (d : ℝ))
    (ε : ℝ) (φ : EuclSpace d → ℝ) (x : EuclSpace d) {e₁ e₂ : ℝ}
    (hS : (sSup (φ '' ball x ε) + sInf (φ '' ball x ε)) / 2
        = φ x + (ε ^ 2 / 2)
            * infLaplacianOf (gradient φ x) (fderiv ℝ (fderiv ℝ φ) x) + e₁)
    (hA : (⨍ y in ball x ε, φ y)
        = φ x + ε ^ 2 / (2 * ((d : ℝ) + 2))
            * laplacianOf (fderiv ℝ (fderiv ℝ φ) x) + e₂) :
    tugOfWarOp p ε φ x
      = φ x + ε ^ 2 / (2 * (p + (d : ℝ)))
          * normPLapOf p (gradient φ x) (fderiv ℝ (fderiv ℝ φ) x)
        + ((p - 2) / (p + (d : ℝ)) * e₁
            + ((d : ℝ) + 2) / (p + (d : ℝ)) * e₂) := by
  rw [tugOfWarOp_expansion p hpd ε φ x hS hA,
      bracket_eq_normPLap p (gradient φ x) (fderiv ℝ (fderiv ℝ φ) x)]

end

end PLaplacian
