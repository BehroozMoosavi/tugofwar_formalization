/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Plaplacian.Discharge

/-!
# The point and index selection

`exists_sel` is equation (2.8) of Luiro-Parviainen-Saksman, and discharges the
hypothesis `hsel` of `deficitLimit_eq_zero`: choose a point nearly attaining
the deficit supremum at stage `k+1`, then a late index at that same point, and
subtract to obtain

  `w (l+1) x0 - w (k+1) x0 >= M - 2 delta`.

`le_deficitSup_of_antitone` supplies its hypothesis that every stage's deficit
supremum is at least `M`, which holds because the suprema are antitone with
limit `M`.

## Main results

- `exists_sel`, `le_deficitSup_of_antitone`
-/

open MeasureTheory Metric Set Filter

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-- **LPS's (2.8).**

Pick `x_0` nearly attaining the deficit supremum at stage `k+1`, so that
`u(x_0) - u_{k+1}(x_0) >= M - delta`. Then pick a late index `l` with
`u(x_0) - u_{l+1}(x_0) < delta`. Subtracting,

  `u_{l+1}(x_0) - u_{k+1}(x_0) >= M - 2 delta`,

which is the chained estimate's left-hand side since the iterates at `l+1` and
`k+1` are the operator applied at `l` and `k`.
-/
theorem exists_sel {S : Set (EuclSpace d)} (hS : S.Nonempty)
    {u : EuclSpace d → ℝ} {w : ℕ → EuclSpace d → ℝ} {M δ : ℝ} (hδ : 0 < δ)
    (hMk : ∀ k, M ≤ deficitSup S u (w (k + 1)))
    (hconv : ∀ x, Tendsto (fun j => w j x) atTop (nhds (u x)))
    (k : ℕ) :
    ∃ x₀ ∈ S, ∃ l : ℕ, M - 2 * δ ≤ w (l + 1) x₀ - w (k + 1) x₀ := by
  obtain ⟨x₀, hx₀S, hx₀⟩ :=
    exists_point_near (S := S) hS (u := u) (w := w (k + 1)) hδ
  obtain ⟨l, -, hl⟩ := exists_late_index (u := u) (w := w) hδ (hconv x₀) k
  refine ⟨x₀, hx₀S, l, ?_⟩
  have h1 : M - δ ≤ u x₀ - w (k + 1) x₀ := by
    have := hMk k
    linarith [hx₀]
  linarith [hl]

/-- The deficit supremum is at least `M` at every stage, since the suprema
decrease to `M`. -/
theorem le_deficitSup_of_antitone {S : Set (EuclSpace d)} (hS : S.Nonempty)
    {u : EuclSpace d → ℝ} {w : ℕ → EuclSpace d → ℝ} {M C : ℝ}
    (hC : ∀ j x, |u x - w j x| ≤ C)
    (hmono : ∀ j x, w j x ≤ w (j + 1) x)
    (hlim : Tendsto (fun j => deficitSup S u (w j)) atTop (nhds M))
    (k : ℕ) :
    M ≤ deficitSup S u (w k) := by
  have hanti := deficitSup_antitone hS hC hmono
  refine le_of_tendsto hlim (Filter.eventually_atTop.2 ⟨k, fun j hj => ?_⟩)
  exact hanti hj

end

end PLaplacian
