/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.OpLocal

/-!
# The comparison with a local hypothesis

The comparison through the operator, restated to need the bound only on the
ball, which is what local monotonicity permits and what the viscosity
predicate supplies. A local maximum of the difference gives a radius, and for
a parameter below that radius the bound on the ball follows.

The restatement also drops the dimension hypothesis the global version
carried, local monotonicity not requiring it.

## Main results

- dpp_comparison_local
- dpp_comparison_local'
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The comparison with a local hypothesis

`dpp_comparison` wanted the bound everywhere; `tugOfWarOp_mono_ball` shows the
operator only needs it on the ball. Restating accordingly, the comparison now
accepts what the viscosity predicate supplies.
-/


/-- **The comparison through the operator, local form.**

If the difference is bounded by `c` on the ball of radius `ε` about `y`, with
equality at `y`, and `u` is `p`-harmonious at `y`, then `φ` satisfies the
discrete inequality there. -/
theorem dpp_comparison_local {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F u φ : EuclSpace d → ℝ}
    (hu : IsPHarmonious p ε Ω F u) (hφ : BddMeas φ)
    {y : EuclSpace d} (hy : y ∈ Ω) {c : ℝ}
    (hle : ∀ w ∈ ball y ε, u w - φ w ≤ c) (heq : u y - φ y = c) :
    φ y ≤ tugOfWarOp p ε φ y := by
  -- u ≤ φ + c on the ball
  have hup : ∀ w ∈ ball y ε, u w ≤ φ w + c := by
    intro w hw
    linarith [hle w hw]
  -- the shifted test function is admissible
  have hψ : BddMeas (fun w => φ w + c) := bddMeas_add_const hφ c
  -- local monotonicity
  have hmono : tugOfWarOp p ε u y
      ≤ tugOfWarOp p ε (fun w => φ w + c) y :=
    tugOfWarOp_mono_ball p ε hp hε hpd hu.bddMeas hψ y hup
  -- the constant comes out
  rw [tugOfWarOp_add_const p ε hε hφ c y hpd] at hmono
  -- the dynamic programming principle
  rw [← hu.interior y hy] at hmono
  have huy : u y = φ y + c := by linarith [heq]
  rw [huy] at hmono
  linarith [hmono]

/-- The version needing no separate equality, the constant being the value at
the point. -/
theorem dpp_comparison_local' {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F u φ : EuclSpace d → ℝ}
    (hu : IsPHarmonious p ε Ω F u) (hφ : BddMeas φ)
    {y : EuclSpace d} (hy : y ∈ Ω)
    (hle : ∀ w ∈ ball y ε, u w - φ w ≤ u y - φ y) :
    φ y ≤ tugOfWarOp p ε φ y :=
  dpp_comparison_local hp hε hpd hu hφ hy hle rfl

end

end PLaplacian
