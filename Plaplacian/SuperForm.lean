/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.DiffMin

@[expose] public section

/-!
# The supersolution's limit passage and predicate form

The duals of the subsolution's. A quantity bounded above by terms tending to
zero is nonpositive, and the generator being minus the operator, nonpositivity
of the operator is nonnegativity of the generator, which is what the
supersolution predicate requires of the homogeneous equation.

The supersolution predicate mirrors the subsolution one field for field: lower
semicontinuity in place of upper, a local minimum in place of a maximum, the
inequality reversed, and the upper envelope in place of the lower at the
singular set. So both halves of the convergence layer now stand at the same
point: every input proved, only the quantifier assembly outstanding, and the
supersolution assembly is the mirror of the one documented for the
subsolution.

## Main results

- nonpos_of_rate
- le_viscF_of_nonpos, le_viscF_of_chain
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The supersolution's limit passage and predicate form

The duals of `nonneg_of_rate` and `viscF_le_of_chain`. A quantity bounded
above by terms tending to zero is nonpositive; and `viscF` being minus the
operator, nonpositivity of the operator is `0 ≤ viscF`, which is the
supersolution inequality for the homogeneous equation.
-/


/-- **The dual limit argument.** A quantity bounded above by terms tending to
zero is nonpositive. -/
theorem nonpos_of_rate {I : ℝ} {q : ℝ → ℝ}
    (hq : Filter.Tendsto q (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hle : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), I ≤ q ε) :
    I ≤ 0 :=
  ge_of_tendsto hq hle

/-- **The predicate's requirement for a supersolution.** -/
theorem le_viscF_of_nonpos {p : ℝ} {q : EuclSpace d}
    {X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ}
    (h : normPLapOf p q X ≤ 0) :
    0 ≤ viscF p q X := by
  rw [viscF_eq_neg]
  linarith [h]

/-- In the predicate's exact notation. -/
theorem le_viscF_of_chain {p : ℝ} {φ : EuclSpace d → ℝ} {x : EuclSpace d}
    (h : normPLapOf p (gradient φ x) (fderiv ℝ (fderiv ℝ φ) x) ≤ 0) :
    0 ≤ viscF p (gradient φ x) (hess φ x) := by
  rw [hess_eq_fderiv]
  exact le_viscF_of_nonpos h

end

end PLaplacian
