/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.AtPair

@[expose] public section

/-!
# The approximate comparison

The near-contact gives the difference within a slack of its bound, not equal
to it, and the comparison as proved wants equality. The gap closes by carrying
the slack into the conclusion, where it passes through the expansion as an
additive term and vanishes in the limit, the slack being arbitrary.

So the inexactness of the near-contact, which traces back to a solution being
bounded and Borel rather than continuous, costs an extra quantifier and not a
different argument. We had flagged it as possibly obstructive and it is not.

## Main results

- dpp_comparison_approx
- diff_at_pair_approx
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The approximate comparison

The near-contact gives the difference within `κ` of its bound, not equal to
it, and the comparison as proved wants equality. The gap closes with a slack
in the conclusion.

If `u - φ ≤ c` on the ball and `u y - φ y ≥ c - κ`, then:

  monotonicity and equivariance give `u y = T_ε u y ≤ T_ε φ y + c`;
  the near-equality gives `u y ≥ φ y + c - κ`;
  hence `φ y + c - κ ≤ T_ε φ y + c`, that is `φ y ≤ T_ε φ y + κ`.

The slack `κ` passes into the differential inequality as an additive term and
vanishes in the limit, `κ` being arbitrary. This is the step that the exact
comparison could not supply, and it is why the near-contact's inexactness does
not obstruct the argument.
-/


/-- **The approximate comparison.** -/
theorem dpp_comparison_approx {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F u φ : EuclSpace d → ℝ}
    (hu : IsPHarmonious p ε Ω F u) (hφ : BddMeas φ)
    {y : EuclSpace d} (hy : y ∈ Ω) {c κ : ℝ}
    (hle : ∀ w ∈ ball y ε, u w - φ w ≤ c)
    (hnear : c - κ ≤ u y - φ y) :
    φ y ≤ tugOfWarOp p ε φ y + κ := by
  -- u ≤ φ + c on the ball
  have hup : ∀ w ∈ ball y ε, u w ≤ φ w + c := by
    intro w hw
    linarith [hle w hw]
  have hψ : BddMeas (fun w => φ w + c) := bddMeas_add_const hφ c
  -- monotonicity
  have hmono : tugOfWarOp p ε u y
      ≤ tugOfWarOp p ε (fun w => φ w + c) y :=
    tugOfWarOp_mono_ball p ε hp hε hpd hu.bddMeas hψ y hup
  rw [tugOfWarOp_add_const p ε hε hφ c y hpd] at hmono
  -- the dynamic programming principle
  rw [← hu.interior y hy] at hmono
  -- and the near-equality
  linarith [hmono, hnear]

/-- **The differential inequality with slack.** -/
theorem diff_at_pair_approx [Nontrivial (EuclSpace d)] {p : ℝ} (hp : 2 ≤ p)
    (hd : 0 < d) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F φ : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ}
    {q : ℝ × EuclSpace d} (hq1 : 0 < q.1)
    (hu : IsPHarmonious p q.1 Ω F (u q.1))
    (hφ : ContDiff ℝ 3 φ) (hφb : BddMeas φ)
    (hmem : q.2 ∈ Ω) (hgrad : gradient φ q.2 ≠ 0) {c κ : ℝ}
    (hle : ∀ w ∈ ball q.2 q.1, u q.1 w - φ w ≤ c)
    (hnear : c - κ ≤ u q.1 q.2 - φ q.2) :
    ∃ E : ℝ,
      0 ≤ q.1 ^ 2 / (2 * (p + (d : ℝ)))
          * normPLapOf p (gradient φ q.2) (fderiv ℝ (fderiv ℝ φ) q.2)
        + E + κ := by
  obtain ⟨E, hE⟩ := tugOfWarOp_expansion_final hd p hpd hφ hgrad hq1
  refine ⟨E, ?_⟩
  have hcmp := dpp_comparison_approx hp hq1 hpd hu hφb hmem hle hnear
  rw [hE] at hcmp
  linarith [hcmp]

end

end PLaplacian
