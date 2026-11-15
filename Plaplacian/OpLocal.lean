/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.LocalMono

@[expose] public section

/-!
# The operator is locally monotone

The three pieces combined through the operator expression. For p at least two
both weights are nonnegative, so an inequality on the ball gives an inequality
of the weighted combinations.

The boundedness of the image and the integrability on the ball are built here
from the definition of the admissible class, rather than taken from named
lemmas: the first layer used those facts inside its measurability proof but
never extracted them.

## Main results

- weights_nonneg
- tugOfWarOp_mono_ball
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The operator is locally monotone

Combining the three pieces through the operator's expression. For `2 ≤ p` both
weights are nonnegative, so an inequality on the ball gives an inequality of
the weighted combinations.
-/


/-- The weights are nonnegative for `2 ≤ p`. -/
theorem weights_nonneg (p : ℝ) (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ)) :
    0 ≤ (p - 2) / (p + (d : ℝ)) ∧ 0 ≤ ((d : ℝ) + 2) / (p + (d : ℝ)) := by
  constructor
  · exact div_nonneg (by linarith) (le_of_lt hpd)
  · exact div_nonneg (by positivity) (le_of_lt hpd)

/-- **Local monotonicity of the operator.** -/
theorem tugOfWarOp_mono_ball (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ)) {u v : EuclSpace d → ℝ}
    (hu : BddMeas u) (hv : BddMeas v) (x : EuclSpace d)
    (hle : ∀ w ∈ ball x ε, u w ≤ v w) :
    tugOfWarOp p ε u x ≤ tugOfWarOp p ε v x := by
  obtain ⟨hα, hβ⟩ := weights_nonneg (d := d) p hp hpd
  rw [tugOfWarOp_eq, tugOfWarOp_eq]
  -- the extreme values
  have hsup : sSup (u '' ball x ε) ≤ sSup (v '' ball x ε) := by
    refine sSup_ball_mono hε hle ?_
    obtain ⟨B, hB⟩ := hv.bound
    refine ⟨B, ?_⟩
    rintro a ⟨w, hw, rfl⟩
    exact le_of_abs_le (hB w)
  have hinf : sInf (u '' ball x ε) ≤ sInf (v '' ball x ε) := by
    refine sInf_ball_mono hε hle ?_
    obtain ⟨B, hB⟩ := hu.bound
    refine ⟨- B, ?_⟩
    rintro a ⟨w, hw, rfl⟩
    exact (abs_le.1 (hB w)).1
  -- the average
  have havg : (⨍ y in ball x ε, u y) ≤ ⨍ y in ball x ε, v y := by
    refine setAverage_ball_mono hle ?_ ?_
    · exact hu.integrableOn_ball x ε
    · exact hv.integrableOn_ball x ε
  -- combine
  have h1 : (sSup (u '' ball x ε) + sInf (u '' ball x ε)) / 2
      ≤ (sSup (v '' ball x ε) + sInf (v '' ball x ε)) / 2 := by
    linarith [hsup, hinf]
  nlinarith [h1, havg, hα, hβ]

end

end PLaplacian
