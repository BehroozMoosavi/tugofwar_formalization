/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Plaplacian.StepOperator

/-!
# The boundary strip and the ε-Dirichlet problem

The step operator at a point `x` reads the values of `v` on the open ball
`ball x ε`. So for the discrete problem on a domain `Ω` the data must be
prescribed not on `∂Ω` but on a *strip* of width `ε` outside `Ω`. This file
defines that strip, the ε-Dirichlet problem, and the containment lemma that
makes the formulation well posed.

## The inequality in the strip

For `x ∈ Ω`, every point `y` of the open ball `ball x ε` satisfies
`dist y Ω ≤ dist y x < ε`, so the operator never reads a point at distance
exactly `ε` from `Ω`, and a strip defined with `<` would determine it as well.
We take `≤`, which makes the closed ball `closedBall x ε` lie in
`Ω ∪ bdryStrip Ω ε` (`closedBall_subset_union`), since the points of its sphere
may lie at distance exactly `ε`.

## Main definitions

- `bdryStrip Ω ε`: the strip `{x ∉ Ω : dist x Ω ≤ ε}`.
- `closureEps Ω ε`: the union `Ω ∪ bdryStrip Ω ε`, where the data lives.
- `IsPHarmonious p ε Ω F u`: `u` is bounded measurable, satisfies the dynamic
  programming equation `u = T_ε u` on `Ω`, and equals `F` on the strip.

## Main results

- `disjoint_bdryStrip`: the strip and the domain are disjoint.
- `closedBall_subset_union`: for `x ∈ Ω`, `closedBall x ε ⊆ Ω ∪ bdryStrip Ω ε`.
  This is the statement that the ε-problem is closed: the operator never reads
  a point where no data is available.

## TODO

- The discrete comparison principle, by perturbing with the strict concave
  function `ψ x = R ^ 2 - ‖x‖ ^ 2`. Nonexpansiveness alone is insufficient.
- Existence and uniqueness of `p`-harmonious functions, with the bounds
  `min F ≤ u ≤ max F`.
-/

open MeasureTheory Metric Set

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-- The boundary strip: points outside `Ω` within distance `ε` of it.

The `≤` makes `closedBall_subset_union` hold; see the module docstring. -/
def bdryStrip (Ω : Set (EuclSpace d)) (ε : ℝ) : Set (EuclSpace d) :=
  {x | x ∉ Ω ∧ Metric.infDist x Ω ≤ ε}

/-- The set on which the data of the ε-problem is prescribed. -/
def closureEps (Ω : Set (EuclSpace d)) (ε : ℝ) : Set (EuclSpace d) :=
  Ω ∪ bdryStrip Ω ε

lemma disjoint_bdryStrip (Ω : Set (EuclSpace d)) (ε : ℝ) :
    Disjoint Ω (bdryStrip Ω ε) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  exact hx'.1 hx

lemma subset_closureEps (Ω : Set (EuclSpace d)) (ε : ℝ) :
    Ω ⊆ closureEps Ω ε := Set.subset_union_left

/-- **The ε-problem is closed.** At a point of `Ω` the operator reads only
points of `Ω ∪ Γ_ε`, so it never needs a value that is not prescribed. -/
lemma closedBall_subset_union (Ω : Set (EuclSpace d)) {ε : ℝ}
    {x : EuclSpace d} (hx : x ∈ Ω) :
    closedBall x ε ⊆ Ω ∪ bdryStrip Ω ε := by
  intro y hy
  by_cases hyΩ : y ∈ Ω
  · exact Or.inl hyΩ
  · refine Or.inr ⟨hyΩ, ?_⟩
    calc Metric.infDist y Ω ≤ dist y x := Metric.infDist_le_dist_of_mem hx
      _ ≤ ε := Metric.mem_closedBall.1 hy

/-- **The ε-Dirichlet problem.** The dynamic programming principle is taken as
the definition of the discrete problem, not derived from a game. -/
structure IsPHarmonious (p ε : ℝ) (Ω : Set (EuclSpace d))
    (F : EuclSpace d → ℝ) (u : EuclSpace d → ℝ) : Prop where
  bddMeas : BddMeas u
  interior : ∀ x ∈ Ω, u x = tugOfWarOp p ε u x
  boundary : ∀ x ∈ bdryStrip Ω ε, u x = F x

end PLaplacian
