/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.C2Expand

@[expose] public section

/-!
# The subsolution inequality in predicate form

The generator of the second layer is minus the operator by definition, and the
Hessian notation of the predicate is the iterated derivative of ours. So the
conclusion the convergence chain produces, that the normalized p-Laplacian is
nonnegative, is exactly what the predicate requires of a subsolution of the
homogeneous equation.

With this, all three obstacles found while attempting the assembly are
cleared: the predicate tests with C two functions, which the C two estimate
supplies; it gives a local maximum, which the local comparison accepts; and
its generator differs from ours by a sign.

## Main results

- viscF_eq_neg, hess_eq_fderiv
- viscF_le_of_chain
-/

open Set Topology Filter MeasureTheory Metric Asymptotics

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The subsolution inequality in predicate form

`viscF` is minus `normPLapOf` by definition, so the inequality our chain
produces, that the normalized `p`-Laplacian is nonnegative, is exactly the
predicate's requirement for the homogeneous equation.
-/


/-- `viscF` is minus the operator. -/
theorem viscF_eq_neg (p : ℝ) (q : EuclSpace d)
    (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) :
    viscF p q X = - normPLapOf p q X := rfl

/-- **The predicate's requirement, from the chain's conclusion.**

For the homogeneous equation, nonnegativity of the normalized `p`-Laplacian is
the subsolution inequality. -/
theorem viscF_le_zero_of_nonneg {p : ℝ} {q : EuclSpace d}
    {X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ}
    (h : 0 ≤ normPLapOf p q X) :
    viscF p q X ≤ 0 := by
  rw [viscF_eq_neg]
  linarith [h]

/-- And the Hessian in the predicate's notation is the iterated derivative in
ours. -/
theorem hess_eq_fderiv (φ : EuclSpace d → ℝ) (x : EuclSpace d) :
    hess φ x = fderiv ℝ (fderiv ℝ φ) x := rfl

/-- **The subsolution inequality, in the predicate's exact form.** -/
theorem viscF_le_of_chain {p : ℝ} {φ : EuclSpace d → ℝ} {x : EuclSpace d}
    (h : 0 ≤ normPLapOf p (gradient φ x) (fderiv ℝ (fderiv ℝ φ) x)) :
    viscF p (gradient φ x) (hess φ x) ≤ 0 := by
  rw [hess_eq_fderiv]
  exact viscF_le_zero_of_nonneg h

end

end PLaplacian
