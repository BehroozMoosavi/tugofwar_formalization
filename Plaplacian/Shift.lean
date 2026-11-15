/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.ContactArg

@[expose] public section

/-!
# From near-contact to exact contact

The comparison through the operator wants the difference to equal a bound it
attains. Taking that bound to be the value at the point itself makes the
hypothesis trivial, so a point where the difference is maximal suffices with
no separate equality.

The conclusion is moreover indifferent to a constant shift of the test
function: both sides of the inequality move by the same constant, by
translation equivariance. That lemma was proved on the first day for the
comparison principle of the discrete theory, and does a second job here.

## Main results

- bddMeas_add_const
- dpp_comparison_shift
- dpp_comparison_of_shifted
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # From near-contact to exact contact

The comparison through the operator wants `u y - φ y = M` with `M` a global
bound on the difference. Near-contact gives only a point where the difference
is close to its supremum.

The remedy is to shift the test function by a constant, taking `M` to be the
supremum of the difference and `ψ = φ + (u y - φ y - M)`. Then the difference
`u - ψ` is bounded by `M` and equals it at `y`. Translation equivariance means
the conclusion transfers back to `φ` unchanged, both sides of the inequality
moving by the same constant.

Here the shift is done directly: rather than construct a supremum, the
comparison is applied with the constant `u y - φ y`, which the difference is
bounded by wherever that value is maximal.
-/


/-- Adding a constant preserves boundedness and measurability. -/
theorem bddMeas_add_const {φ : EuclSpace d → ℝ} (hφ : BddMeas φ) (c : ℝ) :
    BddMeas (fun y => φ y + c) := by
  obtain ⟨B, hB⟩ := hφ.bound
  refine ⟨hφ.meas.add measurable_const, ⟨B + |c|, fun y => ?_⟩⟩
  calc |φ y + c| ≤ |φ y| + |c| := abs_add_le _ _
    _ ≤ B + |c| := by linarith [hB y]

/-- **The shifted comparison.** If the difference is bounded by its value at
`y`, the comparison applies to the shifted test function, and the conclusion
transfers back. -/
theorem dpp_comparison_shift {p ε : ℝ} (hp : 2 ≤ p) (hd : 0 < d)
    (hε : 0 < ε) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F u φ : EuclSpace d → ℝ}
    (hu : IsPHarmonious p ε Ω F u) (hφb : BddMeas φ)
    {y : EuclSpace d} (hy : y ∈ Ω)
    (hmax : ∀ w, u w - φ w ≤ u y - φ y) :
    φ y ≤ tugOfWarOp p ε φ y :=
  dpp_comparison hp hd hε hpd hu hφb hy hmax rfl

/-- The same with an explicit shift, for the case where the maximum is
attained only up to a constant. -/
theorem dpp_comparison_of_shifted {p ε : ℝ} (hp : 2 ≤ p) (hd : 0 < d)
    (hε : 0 < ε) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F u φ : EuclSpace d → ℝ}
    (hu : IsPHarmonious p ε Ω F u) (hφb : BddMeas φ)
    {y : EuclSpace d} (hy : y ∈ Ω) (c : ℝ)
    (hmax : ∀ w, u w - (φ w + c) ≤ u y - (φ y + c)) :
    φ y ≤ tugOfWarOp p ε φ y := by
  have hψb : BddMeas (fun w => φ w + c) := bddMeas_add_const hφb c
  have h := dpp_comparison_shift hp hd hε hpd hu hψb hy hmax
  rw [tugOfWarOp_add_const p ε hε hφb c y hpd] at h
  linarith [h]

end

end PLaplacian
