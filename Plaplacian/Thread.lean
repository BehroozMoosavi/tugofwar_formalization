/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Squeeze

@[expose] public section

/-!
# Threading the bounds

The squeeze takes the four sandwich bounds as hypotheses; the four proved
theorems supply them. This file does the application, obtaining the maximizer
and the minimizer and packaging the result: the average of the supremum and
infimum over the open ball equals the value at the centre plus the
infinity-Laplacian term, plus an error squeezed between quantities built from
the Taylor errors and the quadratic comparison terms at those points.

One formalization note. The point and the infinity-Laplacian value are
implicit arguments of the squeeze, and nothing in the four hypotheses pins
them, so they must be supplied by name. Without that the elaborator leaves
metavariables and every arithmetic step fails against them.

## Main results

- extreme_avg_threaded
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## Threading the bounds

`extreme_avg_squeezed_ball` takes the four sandwich bounds as hypotheses. The
four proved theorems supply them, but with the maximizer and minimizer
appearing in the error terms, so the widths are existential.

This file does the threading: obtaining the two extremizers and packaging the
result.
-/


/-- **The extreme-value average, with the error bounded by proved
quantities.**

Obtaining the maximizer and minimizer from the two upper bounds, the average
equals the target plus an error squeezed between quantities built from the
Taylor errors and the quadratic comparison terms at those points. -/
theorem extreme_avg_threaded {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    {x : EuclSpace d} (hx : gradient φ x ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ e lo hi : ℝ,
      (sSup (φ '' ball x ε) + sInf (φ '' ball x ε)) / 2
          = φ x + (ε ^ 2 / 2) * infLaplacianOf (gradient φ x)
              (fderiv ℝ (fderiv ℝ φ) x) + e
        ∧ lo ≤ e ∧ e ≤ hi := by
  -- the supremum, from below
  have hSlow := sSup_lower_infLap hφ hx hε
  -- the supremum, from above, with a maximizer
  obtain ⟨y, hyMem, hSupp⟩ := sSup_upper_infLap hφ hx hε
  -- the infimum, from below, with a minimizer
  obtain ⟨w, hwMem, hIlow⟩ := sInf_lower_infLap hφ hx hε
  -- the infimum, from above
  have hIupp := sInf_upper_infLap hφ hx hε
  -- assemble
  obtain ⟨e, he, hlo, hhi⟩ :=
    extreme_avg_squeezed_ball (x := x) hφ.continuous hε
      (I := infLaplacianOf (gradient φ x) (fderiv ℝ (fderiv ℝ φ) x))
      (loS := taylorErr φ x (ε • gradDir φ x))
      (hiS := (1 / 2) * (‖fderiv ℝ (fderiv ℝ φ) x‖
          * ‖y - x - ε • gradDir φ x‖
          * (‖y - x‖ + ‖ε • gradDir φ x‖))
        + taylorErr φ x (y - x))
      (loI := - (1 / 2) * (‖fderiv ℝ (fderiv ℝ (fun z => -φ z)) x‖
            * ‖w - x - ε • gradDir (fun z => -φ z) x‖
            * (‖w - x‖ + ‖ε • gradDir (fun z => -φ z) x‖))
          - taylorErr (fun z => -φ z) x (w - x))
      (hiI := - taylorErr (fun z => -φ z) x
          (ε • gradDir (fun z => -φ z) x))
      (by linarith [hSlow]) (by linarith [hSupp])
      (by linarith [hIlow]) (by linarith [hIupp])
  exact ⟨e, _, _, he, hlo, hhi⟩

end

end PLaplacian
