/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Thread

@[expose] public section

/-!
# The asymptotic expansion of the step operator

For a three times continuously differentiable test function with nonvanishing
gradient, the step operator applied at a point equals the value there, plus
epsilon squared over twice p plus d times the normalized p-Laplacian, plus an
error term.

This is the theorem the asymptotic layer exists to prove. The two halves are
supplied by the threaded extreme-value average and the average expansion, so
the statement holds outright rather than conditionally.

The constant one over twice p plus d emerges from the moment computations: the
average half contributes the ordinary Laplacian with weight one over twice d
plus two, the extreme-value half contributes the infinity Laplacian with
weight one half, and the operator weights alpha and beta combine them, the
d plus two cancelling.

## Main results

- tugOfWarOp_expansion_final
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The unconditional expansion

`tugOfWarOp_expansion_normPLap` took the two halves as hypotheses.
`extreme_avg_threaded` supplies the extreme-value half and
`setAverage_expansion` the average half, so the expansion holds outright.
-/


/-- **The asymptotic expansion of the step operator.**

For a `C³` test function with nonvanishing gradient, the step operator equals
the value at the point plus the normalized `p`-Laplacian term, plus an error
term. -/
theorem tugOfWarOp_expansion_final [Nontrivial (EuclSpace d)] (hd : 0 < d)
    (p : ℝ) (hpd : 0 < p + (d : ℝ)) {φ : EuclSpace d → ℝ}
    (hφ : ContDiff ℝ 3 φ) {x : EuclSpace d} (hx : gradient φ x ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ E : ℝ,
      tugOfWarOp p ε φ x
        = φ x + ε ^ 2 / (2 * (p + (d : ℝ)))
            * normPLapOf p (gradient φ x) (fderiv ℝ (fderiv ℝ φ) x)
          + E := by
  obtain ⟨e₁, lo, hi, hS, hlo, hhi⟩ := extreme_avg_threaded hφ hx hε
  have hA := setAverage_expansion hd (hφ.of_le (by norm_num)) x hε
  refine ⟨(p - 2) / (p + (d : ℝ)) * e₁
    + ((d : ℝ) + 2) / (p + (d : ℝ))
        * (⨍ z in ball (0 : EuclSpace d) ε, taylorErr φ x z), ?_⟩
  exact tugOfWarOp_expansion_normPLap p hpd ε φ x hS hA

end

end PLaplacian
