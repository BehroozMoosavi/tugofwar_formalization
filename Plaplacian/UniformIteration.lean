/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Plaplacian.Bounds

@[expose] public section

/-!
# Uniform convergence of the Perron iteration

Theorem 2.1 of Luiro-Parviainen-Saksman: the limit of the deficit suprema over
the epsilon-closure is zero, so the Perron iteration converges uniformly. The
three bounds required by `unif_arith` are supplied by `bound_one`, `bound_two`
and `bound_three`.

The limiting inputs and the index selections are taken as hypotheses. They
follow from `tendsto_setIntegral_deficit`, `tendsto_iterLimit` and the LPS
choices of `k`, `x_0` and `l`; keeping them abstract isolates the chained
estimate, which is the substance of the proof.

## Two tolerances, not one

`hglob` carries two independent tolerances. The informal proof writes `delta`
for both the supremum bound (2.6) and the integral bound (2.7), which invites
the reading that they are the same number. They are not: the integral target
must absorb the factor `beta / |B eps|` before it becomes a bound on the
average term, so it is `delta * |B eps| / beta`. Formalizing forces the
distinction.

## Main results

- `deficitLimit_eq_zero`
-/

open MeasureTheory Metric Set Filter

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-- **Uniform convergence of the Perron iteration.** LPS Theorem 2.1.

The two limiting inputs and the index selections are taken as hypotheses; they
follow from `tendsto_setIntegral_deficit`, `tendsto_iterLimit` and the LPS
choices, and are discharged in a wrapper. Keeping them abstract isolates the
chained estimate, which is the substance.

Note that `hglob` carries two independent tolerances. The informal proof writes
`delta` for both the supremum bound and the integral bound, but they play
different roles: the integral target must absorb the factor
`beta / |B eps|` before it becomes a bound on the average term. -/
theorem deficitLimit_eq_zero (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} (_hΩ : Ω.Nonempty)
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C)
    (hstep : ∀ x, u₀ x ≤ tugOfWarOp p ε u₀ x)
    (hBMu : BddMeas (iterLimit p ε u₀))
    {M : ℝ}
    (hglob : ∀ η > 0, ∀ δ' > 0, ∃ k, (∫ y in closureEps Ω ε,
      (iterLimit p ε u₀ y - iter p ε u₀ k y)) ≤ η
      ∧ deficitSup (closureEps Ω ε) (iterLimit p ε u₀)
          (iter p ε u₀ k) ≤ M + δ')
    (hint : ∀ k, MeasureTheory.IntegrableOn
      (fun y => iterLimit p ε u₀ y - iter p ε u₀ k y) (closureEps Ω ε))
    (hsel : ∀ (δ : ℝ), 0 < δ → ∀ k : ℕ, ∃ x₀ ∈ Ω, ∃ l : ℕ,
      M - 2 * δ ≤ tugOfWarOp p ε (iter p ε u₀ l) x₀
        - tugOfWarOp p ε (iter p ε u₀ k) x₀) :
    M ≤ 0 := by
  have hα : (0 : ℝ) ≤ (p - 2) / (p + (d : ℝ)) :=
    div_nonneg (by linarith) hpd.le
  have hβ : (0 : ℝ) < ((d : ℝ) + 2) / (p + (d : ℝ)) := by positivity
  have hvol : (0 : ℝ) < volume.real (ball (0 : EuclSpace d) ε) := by
    have h1 : volume (ball (0 : EuclSpace d) ε) ≠ 0 :=
      measure_ball_ne_zero 0 hε
    have h2 : volume (ball (0 : EuclSpace d) ε) ≠ ⊤ := measure_ball_lt_top.ne
    simp only [MeasureTheory.Measure.real]
    exact ENNReal.toReal_pos h1 h2
  set u := iterLimit p ε u₀ with hu
  have hCd : ∀ j y, |u y - iter p ε u₀ j y| ≤ 2 * C := fun j y =>
    abs_deficit_le p ε hp hε hd hpd hu₀ hC hstep j y
  have hnn : ∀ j y, 0 ≤ u y - iter p ε u₀ j y := fun j y =>
    deficit_nonneg p ε hp hε hd hpd hu₀ hC hstep j y
  have hBM : ∀ j, BddMeas (iter p ε u₀ j) := fun j =>
    bddMeas_iter p ε hp hε hpd hu₀ j
  refine deficitLimit_le_zero hα hβ (alpha_add_beta p hpd) ?_
  intro δ hδ
  -- the target for the global integral, chosen so the average bound is exactly δ
  set η := δ * volume.real (ball (0 : EuclSpace d) ε)
    / (((d : ℝ) + 2) / (p + (d : ℝ))) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]; positivity
  have hηeq : ((d : ℝ) + 2) / (p + (d : ℝ))
      * ((volume.real (ball (0 : EuclSpace d) ε))⁻¹ * η) = δ := by
    rw [hηdef]
    field_simp
  obtain ⟨k, hksmall, hksup⟩ := hglob η hηpos δ hδ
  obtain ⟨x₀, hx₀Ω, l, hchain⟩ := hsel δ hδ k
  refine ⟨⨍ y in ball x₀ ε, (u y - iter p ε u₀ k y),
          sSup ((fun y => u y - iter p ε u₀ k y) '' ball x₀ ε),
          ?_, ?_, ?_⟩
  · refine le_trans hchain ?_
    exact bound_one p ε hp hε hpd hBMu (hBM l) (hBM k)
      (fun y => iter_le_iterLimit p ε hp hε hd hpd hu₀ hC hstep l y)
      (hCd k) x₀
  · exact bound_two (hCd k) hksup hx₀Ω hε
  · rw [← hηeq]
    exact bound_three hε (hnn k) (hint k) hx₀Ω hβ.le hksmall

end

end PLaplacian
