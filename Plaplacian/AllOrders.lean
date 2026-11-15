/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.LineBounds

@[expose] public section

/-!
# A uniform constant across orders

The composition bound requires every iterated derivative up to order three
bounded by a single constant on the ball. Compactness and continuity give a
constant at each order, and finiteness of the index set combines them into
one.

## Main results

- exists_bound_order
- exists_bound_all_orders
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## A uniform constant across orders

The composition bound needs `‖iteratedFDeriv ℝ i φ y‖ ≤ C` for every
`i ≤ 3` with a single `C`. Compactness gives a constant per order, and
`Finite.exists_le` combines finitely many into one.
-/


/-- A bound at a single order. -/
theorem exists_bound_order {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x : EuclSpace d) (ε : ℝ) (i : ℕ) (hi : i ≤ 3) :
    ∃ C : ℝ, ∀ y ∈ closedBall x ε, ‖iteratedFDeriv ℝ i φ y‖ ≤ C := by
  have hcont : Continuous (fun y => iteratedFDeriv ℝ i φ y) := by
    refine hφ.continuous_iteratedFDeriv ?_
    exact_mod_cast hi
  exact (isCompact_closedBall x ε).exists_bound_of_continuousOn
    hcont.continuousOn

/-- **A single constant across all orders up to three.** -/
theorem exists_bound_all_orders {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x : EuclSpace d) (ε : ℝ) :
    ∃ C : ℝ, ∀ y ∈ closedBall x ε, ∀ i ≤ 3,
      ‖iteratedFDeriv ℝ i φ y‖ ≤ C := by
  -- a constant for each of the four orders
  choose f hf using fun i : Fin 4 =>
    exists_bound_order hφ x ε i.val (by omega)
  -- their maximum
  obtain ⟨M, hM⟩ := Finite.exists_le f
  refine ⟨M, fun y hy i hi => ?_⟩
  have hi4 : i < 4 := by omega
  have := hf ⟨i, hi4⟩ y hy
  calc ‖iteratedFDeriv ℝ i φ y‖ ≤ f ⟨i, hi4⟩ := this
    _ ≤ M := hM _

end

end PLaplacian
