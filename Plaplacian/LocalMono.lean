/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Subsol

/-!
# Local monotonicity of the operator

The operator at a point is built from the supremum, infimum and average over
the ball of radius epsilon about that point, and from nothing else. So an
inequality holding only on that ball suffices for monotonicity there.

This closes a gap we had not anticipated. The viscosity predicate supplies a
local maximum of the difference; the comparison through the operator, as first
proved, wanted a global bound. Rather than modify the test function outside a
neighbourhood, which is the usual informal remedy, the operator's own locality
suffices: it never looks outside the ball, so a bound on a neighbourhood is
enough once the parameter is small.

The monotonicity of the set average appears here for a third time, having
been proved in the first layer and used in the third.

## Main results

- exists_radius_of_isLocalMax
- sSup_ball_mono, sInf_ball_mono, setAverage_ball_mono
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # Local monotonicity of the operator

The operator at a point is built from the supremum, infimum and average over
the ball of radius `ε` about that point, and from nothing else. So an
inequality holding only on that ball suffices for monotonicity there.

This is what closes the gap between the predicate's local maximum and the
comparison's global bound: the operator never looks outside the ball, so a
bound on a neighbourhood is enough once `ε` is small.
-/

/-- A radius on which a local maximum's bound holds. -/
theorem exists_radius_of_isLocalMax {f : EuclSpace d → ℝ} {x₀ : EuclSpace d}
    (h : IsLocalMax f x₀) :
    ∃ r > 0, ∀ w ∈ ball x₀ r, f w ≤ f x₀ := by
  rw [IsLocalMax, IsMaxFilter, Filter.eventually_iff] at h
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.1 h
  exact ⟨r, hr, fun w hw => hsub hw⟩

/-- The supremum over the ball is monotone under an inequality on the ball. -/
theorem sSup_ball_mono {u v : EuclSpace d → ℝ} {x : EuclSpace d} {ε : ℝ}
    (hε : 0 < ε) (hle : ∀ w ∈ ball x ε, u w ≤ v w)
    (hbdd : BddAbove (v '' ball x ε)) :
    sSup (u '' ball x ε) ≤ sSup (v '' ball x ε) := by
  have hne : (u '' ball x ε).Nonempty := ⟨u x, ⟨x, mem_ball_self hε, rfl⟩⟩
  refine csSup_le hne ?_
  rintro a ⟨w, hw, rfl⟩
  exact le_trans (hle w hw) (le_csSup hbdd ⟨w, hw, rfl⟩)

/-- And the infimum. -/
theorem sInf_ball_mono {u v : EuclSpace d → ℝ} {x : EuclSpace d} {ε : ℝ}
    (hε : 0 < ε) (hle : ∀ w ∈ ball x ε, u w ≤ v w)
    (hbdd : BddBelow (u '' ball x ε)) :
    sInf (u '' ball x ε) ≤ sInf (v '' ball x ε) := by
  have hne : (v '' ball x ε).Nonempty := ⟨v x, ⟨x, mem_ball_self hε, rfl⟩⟩
  refine le_csInf hne ?_
  rintro a ⟨w, hw, rfl⟩
  exact le_trans (csInf_le hbdd ⟨w, hw, rfl⟩) (hle w hw)

/-- The average over the ball is monotone under an inequality on the ball. -/
theorem setAverage_ball_mono {u v : EuclSpace d → ℝ} {x : EuclSpace d}
    {ε : ℝ} (hle : ∀ w ∈ ball x ε, u w ≤ v w)
    (hu : MeasureTheory.IntegrableOn u (ball x ε))
    (hv : MeasureTheory.IntegrableOn v (ball x ε)) :
    (⨍ y in ball x ε, u y) ≤ ⨍ y in ball x ε, v y :=
  setAverage_mono measurableSet_ball hu hv hle

end

end PLaplacian
