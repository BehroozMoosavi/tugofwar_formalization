/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Plaplacian.Iteration

/-!
# The restricted operator

`tugOfWarOp` applies the dynamic programming formula at every point. The
operator that actually appears in Luiro--Parviainen--Saksman
(*On the existence and uniqueness of `p`-harmonious functions*, Differential
Integral Equations 27 (2014), (2.3)) is piecewise:

  `T u x = tugOfWarOp p ε u x` if `x ∈ Ω`, and `T u x = u x` if `x ∈ Γ_ε`.

The distinction is not cosmetic. Only the piecewise operator preserves boundary
values, so only its iteration converges to a solution *with the prescribed
data*. Iterating `tugOfWarOp` would let the values on the strip drift.

## A hypothesis the informal statement hides

Defining the piecewise operator requires deciding membership in `Ω`, and
proving it preserves measurability requires `Ω` to be measurable
(`Measurable.ite`). The informal definition carries no such hypothesis, since
one silently assumes `Ω` open. Formalizing forces `MeasurableSet Ω` into the
statement of `BddMeas.dppOp` and hence into everything downstream.

## Main results

- `dppOp`: the piecewise operator, with unfolding lemmas.
- `dppOp_monotone`: monotone, for `2 ≤ p`.
- `BddMeas.dppOp`: preserves admissibility, given `MeasurableSet Ω`.
-/

open MeasureTheory Metric Set

noncomputable section

variable {d : ℕ}

namespace PLaplacian

open Classical in
/-- The dynamic programming operator: the formula on `Ω`, the identity
elsewhere. `open Classical in` supplies decidability of set membership; it is
scoped to this definition so that no theorem statement below depends on it. -/
def dppOp (p ε : ℝ) (Ω : Set (EuclSpace d)) (v : EuclSpace d → ℝ)
    (x : EuclSpace d) : ℝ :=
  if x ∈ Ω then tugOfWarOp p ε v x else v x

lemma dppOp_of_mem (p ε : ℝ) {Ω : Set (EuclSpace d)} {x : EuclSpace d}
    (hx : x ∈ Ω) (v : EuclSpace d → ℝ) :
    dppOp p ε Ω v x = tugOfWarOp p ε v x := by
  unfold dppOp; simp [hx]

lemma dppOp_of_notMem (p ε : ℝ) {Ω : Set (EuclSpace d)} {x : EuclSpace d}
    (hx : x ∉ Ω) (v : EuclSpace d → ℝ) :
    dppOp p ε Ω v x = v x := by
  unfold dppOp; simp [hx]

/-- Monotonicity. On `Ω` this is `tugOfWarOp_monotone`; off `Ω` it is the
hypothesis itself. -/
theorem dppOp_monotone (p ε : ℝ) (hp : 2 ≤ p) (hd : 0 < d) (hε : 0 < ε)
    (Ω : Set (EuclSpace d))
    {u v : EuclSpace d → ℝ} (hu : BddMeas u) (hv : BddMeas v)
    (h : ∀ y, u y ≤ v y) (x : EuclSpace d) :
    dppOp p ε Ω u x ≤ dppOp p ε Ω v x := by
  by_cases hx : x ∈ Ω
  · rw [dppOp_of_mem p ε hx, dppOp_of_mem p ε hx]
    exact tugOfWarOp_monotone p ε hp hd hε hu hv h x
  · rw [dppOp_of_notMem p ε hx, dppOp_of_notMem p ε hx]
    exact h x

/-- **Invariance of the admissible class.** Note the hypothesis
`MeasurableSet Ω`, forced by `Measurable.ite`. -/
theorem BddMeas.dppOp (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} (hΩ : MeasurableSet Ω)
    {v : EuclSpace d → ℝ} (hv : BddMeas v) :
    BddMeas (PLaplacian.dppOp p ε Ω v) := by
  obtain ⟨C, hC⟩ := hv.bound
  have hT := BddMeas.tugOfWarOp p ε hp hε hpd hv
  refine ⟨?_, ⟨C, fun x => ?_⟩⟩
  · exact hT.meas.ite hΩ hv.meas
  · by_cases hx : x ∈ Ω
    · rw [dppOp_of_mem p ε hx]
      exact abs_tugOfWarOp_le p ε hp hε hpd hv hC x
    · rw [dppOp_of_notMem p ε hx]
      exact hC x

/-- The operator fixes the strip, so boundary values are preserved along the
iteration. -/
theorem dppOp_eq_on_compl (p ε : ℝ) (Ω : Set (EuclSpace d))
    (v : EuclSpace d → ℝ) {x : EuclSpace d} (hx : x ∉ Ω) :
    dppOp p ε Ω v x = v x := dppOp_of_notMem p ε hx v

end PLaplacian
