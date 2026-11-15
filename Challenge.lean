/-
Copyright (c) 2026 Juan J. Manfredi and Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan J. Manfredi, Behrooz Moosavi
-/
module

public import Mathlib

/-!
# Convergence of the tug-of-war scheme for the normalized `p`-Laplacian

This file states, using only Mathlib, the main theorem of the development
`PLaplacian`; it is proved in `Solution.lean` (by the library, in
`Plaplacian/DirichletExistence.lean`). The definitions below are copied
verbatim from the library, in the same `open`, `namespace`, `variable` and
`noncomputable` context, so that Comparator can check that they coincide.

## The mathematics

Fix `2 ≤ p < ∞`, a dimension `d ≥ 1` and a step size `ε > 0`. For a bounded
Borel function `v : ℝ^d → ℝ`, the tug-of-war step operator is

  `T_ε v(x) = α/2 (sup_{B_ε(x)} v + inf_{B_ε(x)} v) + β ⨍_{B_ε(x)} v`,
  `α = (p - 2)/(p + d)`,  `β = (d + 2)/(p + d)`,

over the open ball `B_ε(x)` (`tugOfWarOp`). A function `u` is `p`-harmonious
in `Ω` with data `F` if it is bounded and measurable, `u = T_ε u` on `Ω`, and
`u = F` on the strip of points outside `Ω` within distance `ε` of it
(`IsPHarmonious`, `bdryStrip`). The upper and lower half-relaxed limits of a
family `(u_ε)` are `ū(x) = limsup u_ε(y)` and `u̲(x) = liminf u_ε(y)` as
`ε → 0⁺` and `y → x` (`ubar`, `lbar`, along `relaxFilter`).

**The theorem.** Let `Ω ⊆ ℝ^d` be bounded and open, satisfying the exterior
sphere condition: every boundary point `y` lies on the sphere of a ball
`B(z, δ)` disjoint from `Ω` (hypothesis `hext`, written as `‖y - z‖ = δ` and
`δ ≤ ‖x - z‖` for all `x ∈ Ω`). Let `F : ℝ^d → ℝ` be continuous with
`|F| ≤ C`. Then there is a family `(u_ε)` such that, for every `ε > 0`, `u_ε`
is `p`-harmonious in `Ω` with data `F` and equals `F` outside `Ω`; every
`u_ε` is bounded by `C`; the relaxed limits agree on the closure of `Ω` and
equal `F` on its boundary; and `u_ε → ū` uniformly on the closure of `Ω` as
`ε → 0⁺`.

## Scope of the compared statement

* The statement asserts existence of the family, the bound, the agreement of
  the relaxed limits, the boundary values and uniform convergence. It does not
  itself assert that the limit is a viscosity solution of `-Δ_p^N u = 0`, nor
  uniqueness. Those are proved in the library and used in the proof:
  `ubar_isViscositySubsolution`, `lbar_isViscositySupersolution` (the limit is
  a viscosity solution), `visc_comparison` and `visc_unique` (comparison and
  uniqueness for the limit equation), and `pharmonious_unique` (uniqueness of
  `u_ε` for each `ε`).
* The hypotheses `0 < p + d` and `Nontrivial (EuclSpace d)` follow from
  `2 ≤ p` and `0 < d`; they are stated explicitly, as in the library.
* `u ε` is required to equal `F` on all of the complement of `Ω`, not only on
  the strip: the relaxed limits at a boundary point see values at distance
  more than `ε` from `Ω`. For `ε ≤ 0`, `u ε` is unconstrained except by the
  bound `C`.
* The domain condition is the exterior sphere condition at every boundary
  point, with a ball that may depend on the point.

The development depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.
-/

@[expose] public section

/-- The ambient Euclidean space `ℝ^d`. `abbrev`, not `def`, so instance search
sees through it. -/
abbrev EuclSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

section Scheme

open MeasureTheory Metric Set

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-- Bounded and measurable: the class on which the step operator is defined. -/
structure BddMeas (v : EuclSpace d → ℝ) : Prop where
  meas : Measurable v
  bound : ∃ C, ∀ y, |v y| ≤ C

/-- **The tug-of-war step operator**, with extreme values and average over the
open ball `ball x ε`. -/
def tugOfWarOp (p ε : ℝ) (v : EuclSpace d → ℝ) (x : EuclSpace d) : ℝ :=
  (p - 2) / (p + (d : ℝ)) / 2 *
      (sSup (v '' ball x ε) + sInf (v '' ball x ε))
    + ((d : ℝ) + 2) / (p + (d : ℝ)) * (⨍ y in ball x ε, v y)

/-- The boundary strip: points outside `Ω` within distance `ε` of it. -/
def bdryStrip (Ω : Set (EuclSpace d)) (ε : ℝ) : Set (EuclSpace d) :=
  {x | x ∉ Ω ∧ Metric.infDist x Ω ≤ ε}

/-- **The ε-Dirichlet problem.** The dynamic programming principle is taken as
the definition of the discrete problem, not derived from a game. -/
structure IsPHarmonious (p ε : ℝ) (Ω : Set (EuclSpace d))
    (F : EuclSpace d → ℝ) (u : EuclSpace d → ℝ) : Prop where
  bddMeas : BddMeas u
  interior : ∀ x ∈ Ω, u x = tugOfWarOp p ε u x
  boundary : ∀ x ∈ bdryStrip Ω ε, u x = F x

end PLaplacian

end

end Scheme

section Relaxed

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-- The filter along which the limits are taken: `ε → 0⁺` and `y → x`. -/
def relaxFilter (x : EuclSpace d) : Filter (ℝ × EuclSpace d) :=
  (nhdsWithin (0 : ℝ) (Set.Ioi 0)) ×ˢ (nhds x)

/-- The upper half-relaxed limit. -/
def ubar (u : ℝ → EuclSpace d → ℝ) (x : EuclSpace d) : ℝ :=
  Filter.limsup (fun q : ℝ × EuclSpace d => u q.1 q.2) (relaxFilter x)

/-- The lower half-relaxed limit. -/
def lbar (u : ℝ → EuclSpace d → ℝ) (x : EuclSpace d) : ℝ :=
  Filter.liminf (fun q : ℝ × EuclSpace d => u q.1 q.2) (relaxFilter x)

end

end PLaplacian

end Relaxed

section MainTheorem

open MeasureTheory Metric Set Filter Topology

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-- **Existence and convergence.** Let `Ω` be bounded and open with an exterior
sphere at every boundary point, and `F` bounded and continuous. Then for every
`ε > 0` the `ε`-problem has a `p`-harmonious solution with data `F`, equal to
`F` outside `Ω`, and these solutions converge uniformly on `closure Ω` to the
common value of the relaxed limits, which equals `F` on `frontier Ω`. -/
theorem pharmonious_exists_converge [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) {F : EuclSpace d → ℝ}
    (hFc : Continuous F) {C : ℝ} (hFC : ∀ y, |F y| ≤ C)
    (hext : ∀ y ∈ frontier Ω, ∃ (z : EuclSpace d) (δ : ℝ), 0 < δ ∧
      ‖y - z‖ = δ ∧ ∀ x ∈ Ω, δ ≤ ‖x - z‖) :
    ∃ u : ℝ → EuclSpace d → ℝ,
      (∀ ε > 0, IsPHarmonious p ε Ω F (u ε)) ∧
      (∀ ε > 0, ∀ x, x ∉ Ω → u ε x = F x) ∧
      (∀ ε y, |u ε y| ≤ C) ∧
      (∀ x ∈ closure Ω, ubar u x = lbar u x) ∧
      (∀ x ∈ frontier Ω, ubar u x = F x) ∧
      (∀ η > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → ∀ x ∈ closure Ω,
        |u ε x - ubar u x| ≤ η) := by
  sorry

end

end PLaplacian

end MainTheorem
