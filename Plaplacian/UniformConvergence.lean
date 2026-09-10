/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Plaplacian.DppOperator

/-!
# The arithmetic core of uniform convergence

Luiro--Parviainen--Saksman prove that the Perron iteration converges
*uniformly*, not merely pointwise, and remark that `β > 0` is needed both for
that and for the limit to satisfy the dynamic programming principle
(*On the existence and uniqueness of `p`-harmonious functions*, Differential
Integral Equations 27 (2014), Thm. 2.1).

Their argument assumes `M := lim_j sup_{Ω_ε} (u - u_j) > 0`, fixes `δ > 0`,
chooses `k` with `u - u_k ≤ M + δ` and with the averages of `u - u_k` uniformly
below `δ`, then chooses `x₀` nearly attaining `M` and `ℓ > k` with
`u_{ℓ+1}(x₀) - u_{k+1}(x₀) ≥ M - 2δ`. Chaining the difference estimates gives
`β M ≤ δ (3 + α)`, and letting `δ → 0` contradicts `M > 0`.

This file isolates the two purely arithmetic steps, so that the main proof is
left with only the index selection. Separating them exposes something the
informal presentation obscures: the chained inequality needs neither `β > 0`
nor `δ > 0`; it is algebra. `β > 0` enters only in the limiting step
`le_zero_of_forall_lt`.

## Main results

- `unif_arith`: from the three chained bounds, `β M ≤ δ (3 + α)`.
- `le_zero_of_forall_lt`: if that holds for every `δ > 0` and `β > 0`, then
  `M ≤ 0`.
-/

open MeasureTheory Metric Set

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-- **The chained inequality.** Given
`M - 2δ ≤ α S + β A`, `S ≤ M + δ` and `β A ≤ δ`, one has
`β M ≤ δ (3 + α)`.

Note that neither `0 < β` nor `0 < δ` is required: this step is algebra, using
only `α ≥ 0` and `α + β = 1`. -/
theorem unif_arith {α β M δ A S : ℝ}
    (hα : 0 ≤ α) (hab : α + β = 1)
    (h1 : M - 2 * δ ≤ α * S + β * A)
    (hS : S ≤ M + δ)
    (hA : β * A ≤ δ) :
    β * M ≤ δ * (3 + α) := by
  have hstep : α * S ≤ α * (M + δ) := mul_le_mul_of_nonneg_left hS hα
  have hexp : α * (M + δ) = α * M + α * δ := by ring
  have hbm : β * M = M - α * M := by
    have hβα : β = 1 - α := by linarith
    rw [hβα]; ring
  rw [hbm]
  linarith [h1, hstep, hexp, hA]

/-- **The limiting step.** This is where `β > 0` is used: if `β M` is bounded
by an arbitrarily small multiple of `3 + α`, then `M ≤ 0`. -/
theorem le_zero_of_forall_lt {β M α : ℝ} (hβ : 0 < β) (hα : 0 ≤ α)
    (h : ∀ δ > 0, β * M ≤ δ * (3 + α)) : M ≤ 0 := by
  by_contra hcon
  push Not at hcon
  have hpos : 0 < β * M := mul_pos hβ hcon
  obtain ⟨δ, hδpos, hδlt⟩ : ∃ δ > 0, δ * (3 + α) < β * M := by
    refine ⟨(β * M) / (2 * (3 + α)), by positivity, ?_⟩
    have h3 : 0 < 3 + α := by linarith
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [hpos, h3]
  exact absurd (h δ hδpos) (not_le.2 hδlt)

end PLaplacian
