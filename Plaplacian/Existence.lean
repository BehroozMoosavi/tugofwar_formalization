/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Plaplacian.UnifContinuity

@[expose] public section

/-!
# Existence of a solution of the dynamic programming principle

Theorem 2.1 of Luiro-Parviainen-Saksman, assembled. From an admissible
subsolution the Perron iteration converges to an admissible fixed point of the
step operator.

The fixed-point property is obtained by passing the operator through the limit.
`T` of the limit is within `eta` of `T` of the `N`-th iterate by
nonexpansiveness, and `T` of the `N`-th iterate is the `(N+1)`-st, which is
within `eta` of the limit by uniform convergence. So the difference is at most
`2 eta` for every positive `eta`, hence zero. Uniform, rather than pointwise,
convergence is what makes this work; see `Plaplacian.UnifContinuity`.

## Main results

- `exists_fixedPoint`
-/

open MeasureTheory Metric Set Filter

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-- **Existence of a solution of the dynamic programming principle.**

Given an admissible subsolution `u₀`, the Perron iteration converges to an
admissible function that is a fixed point of the step operator. This is the
content of Theorem 2.1 of Luiro-Parviainen-Saksman, assembled from the
ingredients proved in the preceding files.

The fixed-point property is obtained by passing the operator through the
limit: `T` of the limit is the limit of the `T`-iterates by
`tugOfWarOp_nonexpansive` together with uniform convergence, and the
`T`-iterates are the iterates shifted by one, whose limit is the same. -/
theorem exists_fixedPoint (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ))
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C)
    (hstep : ∀ x, u₀ x ≤ tugOfWarOp p ε u₀ x)
    (hunif : ∀ η > 0, ∃ N, ∀ j ≥ N, ∀ x,
      |iterLimit p ε u₀ x - iter p ε u₀ j x| ≤ η) :
    BddMeas (iterLimit p ε u₀)
    ∧ ∀ x, tugOfWarOp p ε (iterLimit p ε u₀) x = iterLimit p ε u₀ x := by
  have hBMu := bddMeas_iterLimit p ε hp hε hd hpd hu₀ hC hstep
  refine ⟨hBMu, fun x => ?_⟩
  -- it suffices that the difference is below every positive η
  have key : ∀ η > 0,
      |tugOfWarOp p ε (iterLimit p ε u₀) x - iterLimit p ε u₀ x| ≤ 2 * η := by
    intro η hη
    obtain ⟨N, hN⟩ := hunif η hη
    -- T of the limit is close to T of the N-th iterate
    have h1 : |tugOfWarOp p ε (iterLimit p ε u₀) x
        - tugOfWarOp p ε (iter p ε u₀ N) x| ≤ η :=
      tugOfWarOp_nonexpansive p ε hp hd hε hpd hBMu
        (bddMeas_iter p ε hp hε hpd hu₀ N)
        (fun y => hN N le_rfl y) x
    -- T of the N-th iterate is the (N+1)-st, which is close to the limit
    have h2 : |iterLimit p ε u₀ x - iter p ε u₀ (N + 1) x| ≤ η :=
      hN (N + 1) (Nat.le_succ N) x
    have h3 : iter p ε u₀ (N + 1) x = tugOfWarOp p ε (iter p ε u₀ N) x := rfl
    rw [h3] at h2
    have h4 := abs_le.1 h1
    have h5 := abs_le.1 h2
    rw [abs_le]
    constructor <;> linarith
  -- a nonnegative quantity below every positive bound is zero
  have hzero : tugOfWarOp p ε (iterLimit p ε u₀) x - iterLimit p ε u₀ x = 0 := by
    by_contra hcon
    have hpos : 0 < |tugOfWarOp p ε (iterLimit p ε u₀) x
        - iterLimit p ε u₀ x| := abs_pos.2 hcon
    obtain ⟨η, hηpos, hηlt⟩ : ∃ η > 0, 2 * η
        < |tugOfWarOp p ε (iterLimit p ε u₀) x - iterLimit p ε u₀ x| := by
      refine ⟨|tugOfWarOp p ε (iterLimit p ε u₀) x
        - iterLimit p ε u₀ x| / 4, by positivity, by linarith⟩
    exact absurd (key η hηpos) (not_le.2 hηlt)
  linarith [hzero]

end

end PLaplacian
