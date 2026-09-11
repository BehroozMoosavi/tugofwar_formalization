/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Plaplacian.Dominated

/-!
# Uniform convergence of the Perron iteration

The two steps that turn the arithmetic core of `Plaplacian.UniformConvergence`
into uniform convergence. `deficitLimit_le_zero` performs the quantifier
plumbing: given that for every positive `delta` the three chained bounds can be
produced, the limit `M` of the deficit suprema is nonpositive. Since the
suprema are also nonnegative, `tendsto_deficitSup_zero` concludes that they
converge to zero, which is uniform convergence.

Both are stated for an abstract monotone approximating sequence, so that the
analysis and the quantifier structure are kept apart.

## Main results

- `deficitLimit_le_zero`
- `tendsto_deficitSup_zero`
-/

open MeasureTheory Metric Set Filter

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-- **Uniform convergence, abstract form.**

If the deficit sups converge to `M`, and for every `δ > 0` one can produce the
three bounds of `unif_arith`, then `M ≤ 0` --- i.e. the convergence is
uniform. This isolates the quantifier structure from the analysis. -/
theorem deficitLimit_le_zero {_S : Set (EuclSpace d)}
    {_u : EuclSpace d → ℝ} {_w : ℕ → EuclSpace d → ℝ} {M α β : ℝ}
    (hα : 0 ≤ α) (hβ : 0 < β) (hab : α + β = 1)
    (hkey : ∀ δ > 0, ∃ A S', M - 2 * δ ≤ α * S' + β * A
      ∧ S' ≤ M + δ ∧ β * A ≤ δ) :
    M ≤ 0 := by
  refine le_zero_of_forall_lt hβ hα fun δ hδ => ?_
  obtain ⟨A, S', h1, hS, hA⟩ := hkey δ hδ
  exact unif_arith hα hab h1 hS hA

/-- Uniform convergence follows: the deficit sups converge to `M ≤ 0`, and
being nonnegative they converge to `0`. -/
theorem tendsto_deficitSup_zero {S : Set (EuclSpace d)} (hS : S.Nonempty)
    {u : EuclSpace d → ℝ} {w : ℕ → EuclSpace d → ℝ} {M C : ℝ}
    (hC : ∀ j x, |u x - w j x| ≤ C)
    (hnn : ∀ j x, 0 ≤ u x - w j x)
    (hlim : Tendsto (fun j => deficitSup S u (w j)) atTop (nhds M))
    (hM : M ≤ 0) :
    Tendsto (fun j => deficitSup S u (w j)) atTop (nhds 0) := by
  have hMnn : 0 ≤ M :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall fun j =>
      deficitSup_nonneg hS (hC j) (hnn j))
  have : M = 0 := le_antisymm hM hMnn
  rwa [this] at hlim


end

end PLaplacian
