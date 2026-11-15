/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.LocalizeDist

@[expose] public section

/-!
# The infimum side, by transport

Rather than redo the supremum chain with reversed inequalities, we transport
it through negation. If psi is minus phi then the infimum of phi over a set is
minus the supremum of psi, the gradient of psi is minus that of phi, and so
its normalized direction is minus nu.

Every supremum result already proved therefore applies to psi and yields the
corresponding infimum result for phi, with the linear term acquiring the
opposite sign. That sign flip is exactly the cancellation the expansion needs,
so the transport makes the cancellation structural rather than a coincidence
of two separately computed bounds.

Mathlib has no gradient_neg, so it is proved here from fderiv_neg through the
Riesz representation.

## Main results

- gradient_neg'
- sInf_eq_neg_sSup
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The infimum side

The supremum chain applied to the negation. If `ψ = -φ` then

  `sInf (φ '' S) = - sSup (ψ '' S)`,

and the gradient of `ψ` is minus that of `φ`, so its normalized direction is
`-ν`. The supremum results for `ψ` therefore give the infimum results for `φ`,
with the linear term acquiring the opposite sign --- which is exactly the
cancellation the expansion needs.

Rather than redo the chain, we transport it.
-/


/-- The gradient of the negation. -/
theorem gradient_neg' (φ : EuclSpace d → ℝ) (x : EuclSpace d) :
    gradient (fun y => -φ y) x = - gradient φ x := by
  refine ext_inner_right ℝ fun w => ?_
  rw [inner_gradient_left, inner_neg_left, inner_gradient_left]
  rw [show (fun y => -φ y) = -φ from rfl, fderiv_neg]
  rfl

/-- The negation is `C³` when the function is. -/
theorem contDiff_neg' {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ) :
    ContDiff ℝ 3 (fun y => -φ y) := hφ.neg

/-- Its gradient is nonzero where the original's is. -/
theorem gradient_neg_ne_zero {φ : EuclSpace d → ℝ} {x : EuclSpace d}
    (hx : gradient φ x ≠ 0) : gradient (fun y => -φ y) x ≠ 0 := by
  rw [gradient_neg' φ x]
  exact neg_ne_zero.2 hx

/-- The infimum as minus a supremum. -/
theorem sInf_eq_neg_sSup (φ : EuclSpace d → ℝ) (S : Set (EuclSpace d)) :
    sInf (φ '' S) = - sSup ((fun y => -φ y) '' S) := by
  have himg : (fun y => -φ y) '' S = -(φ '' S) := by
    ext a
    simp only [Set.mem_image, Set.mem_neg]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by ring⟩
    · rintro ⟨y, hy, hay⟩
      exact ⟨y, hy, by linarith [hay]⟩
  rw [himg, Real.sSup_neg]
  ring

end

end PLaplacian
