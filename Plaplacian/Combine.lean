/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.OpenClosed

/-!
# Combining the two halves

The step operator weights the extreme-value term by alpha and the average term
by beta. The two expansions are available: the average gives epsilon squared
over twice d plus two, times the ordinary Laplacian; the average of the
supremum and infimum gives epsilon squared over two, times the infinity
Laplacian, the linear terms having cancelled.

Weighting and adding, the d plus two from the moment computation cancels
against the numerator of beta, leaving the single constant one over twice p
plus d, and the bracket is exactly the normalized p-Laplacian.

That last point is a genuine check rather than a bookkeeping step. The
operator normPLapOf was defined in Plaplacian.Operator from the partial
differential equation, not chosen to make this come out; the asymptotics
independently produce the same combination with the same constant.

## Main results

- combine_weights: the weight arithmetic.
- bracket_eq_normPLap: the bracket is the normalized p-Laplacian.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The asymptotic expansion of the step operator

The operator is

  `T_ε φ x = (α/2)(sup + inf) + β ⨍`,

with `α = (p-2)/(p+d)` and `β = (d+2)/(p+d)`. The two halves are now
available:

* the average gives `φ x + ε²/(2(d+2)) Δφ x + (error)`;
* the extreme values give, in the average of sup and inf,
  `φ x + (ε²/2) Δ^N_∞ φ x + (error)`, the linear terms cancelling.

Weighting and combining:

  `T_ε φ x = φ x + ε²/2 [ α Δ^N_∞ φ x + β/(d+2) Δφ x ] + (error)`
           `= φ x + ε²/(2(p+d)) [ (p-2) Δ^N_∞ φ x + Δφ x ] + (error)`
           `= φ x + ε²/(2(p+d)) Δ^N_p φ x + (error)`,

since `β/(d+2) = 1/(p+d)` and `α = (p-2)/(p+d)`.

This file establishes the arithmetic of that combination, which is the content
of the final step; the error bookkeeping is inherited from the two halves.
-/

/-- The weight identity behind the combination: `β / (d+2) = 1/(p+d)`. -/
theorem beta_div (p : ℝ) (hpd : 0 < p + (d : ℝ)) :
    ((d : ℝ) + 2) / (p + (d : ℝ)) / ((d : ℝ) + 2) = 1 / (p + (d : ℝ)) := by
  have hd2 : ((d : ℝ) + 2) ≠ 0 := by positivity
  field_simp

/-- **The combination identity.** Weighting the two halves by `α` and `β`
produces the normalized `p`-Laplacian, with the constant `1/(2(p+d))`. -/
theorem combine_weights (p : ℝ) (hpd : 0 < p + (d : ℝ)) (ε : ℝ)
    (I L : ℝ) :
    (p - 2) / (p + (d : ℝ)) * ((ε ^ 2 / 2) * I)
        + ((d : ℝ) + 2) / (p + (d : ℝ))
            * (ε ^ 2 / (2 * ((d : ℝ) + 2)) * L)
      = ε ^ 2 / (2 * (p + (d : ℝ))) * ((p - 2) * I + L) := by
  have hd2 : ((d : ℝ) + 2) ≠ 0 := by positivity
  have hpd' : (p + (d : ℝ)) ≠ 0 := ne_of_gt hpd
  field_simp

/-- And the bracket is the normalized `p`-Laplacian. -/
theorem bracket_eq_normPLap (p : ℝ) (q : EuclSpace d)
    (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) :
    (p - 2) * infLaplacianOf q X + laplacianOf X = normPLapOf p q X := by
  unfold normPLapOf
  ring

end

end PLaplacian
