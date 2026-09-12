/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Plaplacian.LimitMeas

/-!
# Discharging the hypotheses of the uniform convergence theorem

`deficitLimit_eq_zero` takes its limiting inputs as hypotheses. This file
supplies two of them.

`exists_index_both` produces a single index satisfying both tolerances. The
informal proof chooses the index sequentially, first for the supremum bound and
then for the integral bound; formally it is cleaner to observe that each
condition holds eventually and intersect the two filters. The two tolerances
remain independent: see the module docstring of
`Plaplacian.UniformIteration`.

`integrableOn_deficit` gives integrability of the deficit on a set of finite
measure, by domination with a constant.

## Main results

- `exists_index_both`, `integrableOn_deficit`
-/

open MeasureTheory Metric Set Filter

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-- **Discharging `hglob`.** Both conditions hold eventually in `j`, so some
single index satisfies both: the integral of the deficit is below `eta` by
dominated convergence, and the deficit supremum is below `M + delta'` because
the suprema decrease to `M`.

The two tolerances are genuinely independent; see the module docstring of
`Plaplacian.UniformIteration`. -/
theorem exists_index_both {S : Set (EuclSpace d)}
    {u : EuclSpace d → ℝ} {w : ℕ → EuclSpace d → ℝ} {M : ℝ}
    (hglob : Tendsto (fun j => ∫ y in S, (u y - w j y)) atTop (nhds 0))
    (hsup : Tendsto (fun j => deficitSup S u (w j)) atTop (nhds M))
    {η : ℝ} (hη : 0 < η) {δ' : ℝ} (hδ' : 0 < δ') :
    ∃ k, (∫ y in S, (u y - w k y)) ≤ η
      ∧ deficitSup S u (w k) ≤ M + δ' := by
  have h1 : ∀ᶠ j in atTop, (∫ y in S, (u y - w j y)) ≤ η :=
    hglob.eventually (eventually_le_nhds hη)
  have h2 : ∀ᶠ j in atTop, deficitSup S u (w j) ≤ M + δ' :=
    hsup.eventually (eventually_le_nhds (by linarith : M < M + δ'))
  obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
  exact ⟨k, hk1, hk2⟩

/-- Integrability of the deficit on a finite-measure set. -/
theorem integrableOn_deficit (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ))
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C)
    (hstep : ∀ x, u₀ x ≤ tugOfWarOp p ε u₀ x)
    {S : Set (EuclSpace d)} (hSfin : volume S ≠ ⊤) (k : ℕ) :
    MeasureTheory.IntegrableOn
      (fun y => iterLimit p ε u₀ y - iter p ε u₀ k y) S := by
  have hBMu := bddMeas_iterLimit p ε hp hε hd hpd hu₀ hC hstep
  have hBMk := bddMeas_iter p ε hp hε hpd hu₀ k
  have hdiff : BddMeas (fun y => iterLimit p ε u₀ y - iter p ε u₀ k y) :=
    hBMu.sub hBMk
  obtain ⟨D, hD⟩ := hdiff.bound
  have hconst : MeasureTheory.IntegrableOn
      (fun _ : EuclSpace d => D) S := by
    refine MeasureTheory.integrableOn_const ?_ ?_
    · exact hSfin
    · simp
  exact hconst.mono' hdiff.meas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by simpa using hD y)

end

end PLaplacian
