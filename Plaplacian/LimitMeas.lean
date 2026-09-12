/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Plaplacian.Bounds

/-!
# Admissibility of the iteration limit

The limit of the Perron iteration is bounded and measurable, hence admissible.
This discharges the hypothesis `BddMeas (iterLimit p eps u0)` of
`deficitLimit_eq_zero`.

Measurability is obtained from `measurable_of_tendsto_metrizable` applied to
the pointwise convergence of `Plaplacian.Iteration`, rather than from
`Measurable.iSup`. Both routes work, since the index set is countable and the
reals are a conditionally complete linear order with second-countable order
topology; the limit form is preferred here because it does not depend on the
limit being a supremum, and so survives if the construction changes.

## Main results

- `measurable_iterLimit`, `abs_iterLimit_le`, `bddMeas_iterLimit`
-/

open MeasureTheory Metric Set Filter

namespace PLaplacian

noncomputable section

variable {d : ℕ}


/-- The limit is measurable, being a pointwise limit of measurable functions.
Uses the pointwise convergence rather than the supremum structure, which avoids
the `iSup` measurability API entirely. -/
theorem measurable_iterLimit (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ))
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C)
    (hstep : ∀ x, u₀ x ≤ tugOfWarOp p ε u₀ x) :
    Measurable (iterLimit p ε u₀) := by
  refine measurable_of_tendsto_metrizable
    (f := fun j => iter p ε u₀ j) ?_ ?_
  · exact fun j => (bddMeas_iter p ε hp hε hpd hu₀ j).meas
  · rw [tendsto_pi_nhds]
    exact fun x => tendsto_iterLimit p ε hp hε hd hpd hu₀ hC hstep x

/-- The limit is bounded, by the bound on the iterates. -/
theorem abs_iterLimit_le (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ))
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C)
    (hstep : ∀ x, u₀ x ≤ tugOfWarOp p ε u₀ x) (x : EuclSpace d) :
    |iterLimit p ε u₀ x| ≤ C := by
  have hlo : -C ≤ iterLimit p ε u₀ x := by
    have h0 := iter_le_iterLimit p ε hp hε hd hpd hu₀ hC hstep 0 x
    simp only [iter_zero] at h0
    linarith [(abs_le.1 (hC x)).1]
  have hhi : iterLimit p ε u₀ x ≤ C := by
    unfold iterLimit
    refine ciSup_le fun i => ?_
    exact (abs_le.1 (abs_iter_le p ε hp hε hpd hu₀ hC i x)).2
  rw [abs_le]
  exact ⟨hlo, hhi⟩

/-- **The limit is admissible.** -/
theorem bddMeas_iterLimit (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ))
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C)
    (hstep : ∀ x, u₀ x ≤ tugOfWarOp p ε u₀ x) :
    BddMeas (iterLimit p ε u₀) :=
  ⟨measurable_iterLimit p ε hp hε hd hpd hu₀ hC hstep,
   ⟨C, abs_iterLimit_le p ε hp hε hd hpd hu₀ hC hstep⟩⟩

end

end PLaplacian
