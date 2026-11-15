/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.TendProd

@[expose] public section

/-!
# The ball containment

The local comparison needs the bound on the ball about the near-contact point;
the local maximum supplies it on the ball about the base point. The containment
holds when the parameter and the displacement are each below half the radius,
by the triangle inequality.

The geometry is isolated from the filter work. The two smallness conditions
hold eventually on the product filter, one in each factor, and an eventual
statement intersected with a frequency is still a frequency. So the
interaction that had been the obstacle reduces to a single application of a
lemma already in the library.

## Main results

- ball_subset_of_near
- eventually_near
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The ball containment

The local comparison needs the bound on `B ε y`; the local maximum supplies it
on `B r x₀`. So `B ε y ⊆ B r x₀` is required, and that holds when the
parameter and the displacement are each below half the radius:

  `‖w - y‖ < ε` and `‖y - x₀‖ < r/2` and `ε < r/2`
  ⟹ `‖w - x₀‖ ≤ ‖w - y‖ + ‖y - x₀‖ < r/2 + r/2 = r`.

Isolated here as pure geometry, with the two smallness conditions as
hypotheses. Establishing them along the filter is the separate step: the
parameter condition is eventual in the first factor, the displacement
condition eventual in the second, and their conjunction eventual on the
product --- so a frequency intersected with it is still a frequency.
-/


/-- **The ball containment.** -/
theorem ball_subset_of_near {x₀ y : EuclSpace d} {ε r : ℝ}
    (hεr : ε < r / 2) (hy : ‖y - x₀‖ < r / 2) :
    ball y ε ⊆ ball x₀ r := by
  intro w hw
  rw [mem_ball, dist_eq_norm] at hw
  rw [mem_ball, dist_eq_norm]
  calc ‖w - x₀‖ = ‖(w - y) + (y - x₀)‖ := by
        congr 1; abel
    _ ≤ ‖w - y‖ + ‖y - x₀‖ := norm_add_le _ _
    _ < r / 2 + r / 2 := by
        exact add_lt_add (lt_trans hw hεr) hy
    _ = r := by ring

/-- The two smallness conditions hold eventually on the product filter. -/
theorem eventually_near {x₀ : EuclSpace d} {r : ℝ} (hr : 0 < r) :
    ∀ᶠ q in relaxFilter x₀,
      q.1 < r / 2 ∧ ‖q.2 - x₀‖ < r / 2 := by
  unfold relaxFilter
  rw [Filter.eventually_iff, Filter.mem_prod_iff]
  refine ⟨Set.Iio (r / 2), ?_, ball x₀ (r / 2), ?_, ?_⟩
  · exact Filter.mem_of_superset (Ioo_mem_nhdsGT (by positivity))
      (fun y hy => hy.2)
  · exact Metric.ball_mem_nhds x₀ (by positivity)
  · intro q hq
    refine ⟨hq.1, ?_⟩
    have := hq.2
    rw [mem_ball, dist_eq_norm] at this
    exact this

end

end PLaplacian
