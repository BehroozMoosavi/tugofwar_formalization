/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.NearMin

/-!
# The comparison at a minimum

The dual of the comparison at a maximum. At a minimum of the difference the
inequality reverses: the operator applied to the test function lies below the
test function.

This one is proved directly rather than transported through negation, and the
distinction is worth recording. Transport works for the relaxed limits because
the limit superior and inferior are genuinely dual under negation. It does not
work for the operator: negating the solution changes the dynamic programming
property, the operator not being odd, since the two weights are fixed and
positive. So the duality that halved the work for the limits has to be paid
for in full here.

## Main results

- dpp_comparison_local_min
- dpp_comparison_local_min'
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The comparison at a minimum

The dual of `dpp_comparison_local`. At a minimum of `u - φ` the inequality
reverses: the operator applied to the test function is below the test
function.

The argument mirrors the maximum case. From `u ≥ φ + c` on the ball,
monotonicity gives `T_ε (φ + c) y ≤ T_ε u y`, equivariance pulls the constant
out, and the dynamic programming principle replaces `T_ε u y` by `u y`, which
equals `φ y + c`.
-/


/-- **The comparison at a minimum.** -/
theorem dpp_comparison_local_min {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F u φ : EuclSpace d → ℝ}
    (hu : IsPHarmonious p ε Ω F u) (hφ : BddMeas φ)
    {y : EuclSpace d} (hy : y ∈ Ω) {c : ℝ}
    (hge : ∀ w ∈ ball y ε, c ≤ u w - φ w) (heq : u y - φ y = c) :
    tugOfWarOp p ε φ y ≤ φ y := by
  -- φ + c ≤ u on the ball
  have hup : ∀ w ∈ ball y ε, φ w + c ≤ u w := by
    intro w hw
    linarith [hge w hw]
  have hψ : BddMeas (fun w => φ w + c) := bddMeas_add_const hφ c
  -- monotonicity, the other way round
  have hmono : tugOfWarOp p ε (fun w => φ w + c) y
      ≤ tugOfWarOp p ε u y :=
    tugOfWarOp_mono_ball p ε hp hε hpd hψ hu.bddMeas y hup
  rw [tugOfWarOp_add_const p ε hε hφ c y hpd] at hmono
  rw [← hu.interior y hy] at hmono
  have huy : u y = φ y + c := by linarith [heq]
  rw [huy] at hmono
  linarith [hmono]

/-- The version needing no separate equality. -/
theorem dpp_comparison_local_min' {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F u φ : EuclSpace d → ℝ}
    (hu : IsPHarmonious p ε Ω F u) (hφ : BddMeas φ)
    {y : EuclSpace d} (hy : y ∈ Ω)
    (hge : ∀ w ∈ ball y ε, u y - φ y ≤ u w - φ w) :
    tugOfWarOp p ε φ y ≤ φ y :=
  dpp_comparison_local_min hp hε hpd hu hφ hy hge rfl

end

end PLaplacian
