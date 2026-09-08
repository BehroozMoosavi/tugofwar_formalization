/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Plaplacian.StepOperator

/-!
# The boundary strip and the ε-Dirichlet problem

The step operator at a point `x` reads the values of `v` on the closed ball
`closedBall x ε`. So for the discrete problem on a domain `Ω` the data must be
prescribed not on `∂Ω` but on a *strip* of width `ε` outside `Ω`. This file
defines that strip, the ε-Dirichlet problem, and the containment lemma that
makes the formulation well posed.

## A correction forced by formalization

The informal literature typically defines the strip with a strict inequality,
`Γ_ε = {x ∉ Ω : dist x Ω < ε}`, while the operator averages over the *closed*
ball of radius `ε`. Those two choices are inconsistent: a point at distance
exactly `ε` from `Ω` is read by the operator but receives no data, so `u` is
underdetermined there. We therefore take `≤` in the strip, which makes
`closedBall_subset_union` exact.

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

Note the `≤`: see the module docstring for why strict inequality would leave
the problem underdetermined. -/
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
