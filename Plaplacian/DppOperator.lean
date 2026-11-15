/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Plaplacian.Iteration

@[expose] public section

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


/-! ### The uniformity bound

The LPS proof of uniform convergence needs

  `sup_{x ∈ Ω} ⨍_{B ε x} (u - u_k) → 0`,

which they obtain from the dominated convergence theorem. Dominated
convergence gives only *pointwise* convergence of the averages, so the
uniformity deserves comment: it holds because the ball volume does not depend
on the centre (`volumeReal_ball_center`), so for a nonnegative integrand the
local average is dominated by the global integral over a fixed set,

  `⨍_{B ε x} f ≤ |B ε|⁻¹ ∫_{Ω_ε} f`,

whose right-hand side is independent of `x`. A single application of dominated
convergence on `Ω_ε` then suffices.
-/

/-- **The uniformity bound.** For a nonnegative function integrable on a set
containing the ball, the average over the ball is dominated by the global
integral divided by the centre-independent ball volume. -/
theorem setAverage_le_integral_div (f : EuclSpace d → ℝ)
    (hnn : ∀ y, 0 ≤ f y) {S : Set (EuclSpace d)}
    (hint : MeasureTheory.IntegrableOn f S) (x : EuclSpace d) {ε : ℝ}
    (hε : 0 < ε) (hsub : ball x ε ⊆ S) :
    (⨍ y in ball x ε, f y)
      ≤ (volume.real (ball (0 : EuclSpace d) ε))⁻¹ * ∫ y in S, f y := by
  rw [MeasureTheory.setAverage_eq, volumeReal_ball_center x ε, smul_eq_mul]
  have hpos : 0 < volume.real (ball (0 : EuclSpace d) ε) := by
    have h1 : volume (ball (0 : EuclSpace d) ε) ≠ 0 :=
      measure_ball_ne_zero 0 hε
    have h2 : volume (ball (0 : EuclSpace d) ε) ≠ ⊤ := measure_ball_lt_top.ne
    simp only [MeasureTheory.Measure.real]
    exact ENNReal.toReal_pos h1 h2
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact MeasureTheory.setIntegral_mono_set hint
    (Filter.Eventually.of_forall hnn) (LE.le.eventuallyLE hsub)

end PLaplacian
