/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Regular

/-!
# Negation and the operator

The operator is odd: under negation the supremum and infimum exchange with a
sign and the average negates. So the negated family is p-harmonious with
negated data, which lets the supersolution be obtained from the subsolution.

## Main results

- bddMeas_neg
- tugOfWarOp_neg
- isPHarmonious_neg
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # Negation and the operator

The regular supersolution follows from the regular subsolution applied to the
negated family and test function. That needs the operator to be odd --- the
supremum and infimum exchange under negation, with signs, and the average
negates --- so that the negated family is `p`-harmonious with negated data.
And it needs the normalized `p`-Laplacian to flip sign when the test function
is negated.
-/


/-- Negation preserves the admissible class. -/
theorem bddMeas_neg {v : EuclSpace d → ℝ} (hv : BddMeas v) :
    BddMeas (fun y => -v y) := by
  obtain ⟨B, hB⟩ := hv.bound
  refine ⟨hv.meas.neg, ⟨B, fun y => ?_⟩⟩
  rw [abs_neg]; exact hB y

/-- **The operator is odd.** -/
theorem tugOfWarOp_neg (p ε : ℝ) (v : EuclSpace d → ℝ) (x : EuclSpace d) :
    tugOfWarOp p ε (fun y => -v y) x = - tugOfWarOp p ε v x := by
  rw [tugOfWarOp_eq, tugOfWarOp_eq]
  have hs : sSup ((fun y => -v y) '' ball x ε) = - sInf (v '' ball x ε) := by
    have := sInf_eq_neg_sSup v (ball x ε)
    linarith
  have hi : sInf ((fun y => -v y) '' ball x ε) = - sSup (v '' ball x ε) := by
    have := sInf_eq_neg_sSup (fun y => -v y) (ball x ε)
    simp only [neg_neg] at this
    exact this
  have ha : (⨍ y in ball x ε, -v y) = - ⨍ y in ball x ε, v y :=
    MeasureTheory.average_neg _ v
  rw [hs, hi, ha]
  ring

/-- **The negated family is `p`-harmonious**, with negated data. -/
theorem isPHarmonious_neg {p ε : ℝ} {Ω : Set (EuclSpace d)}
    {F v : EuclSpace d → ℝ} (hv : IsPHarmonious p ε Ω F v) :
    IsPHarmonious p ε Ω (fun y => -F y) (fun y => -v y) := by
  refine ⟨bddMeas_neg hv.bddMeas, fun x hx => ?_, fun x hx => ?_⟩
  · rw [tugOfWarOp_neg, ← hv.interior x hx]
  · show -v x = -F x
    rw [hv.boundary x hx]

end

end PLaplacian
