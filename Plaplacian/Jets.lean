/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.ViscC2

/-! # Jets, and the statement of the theorem of sums

The comparison principle for the limit equation is proved by doubling the
variables, and its analytic core is the theorem of sums of Crandall, Ishii and
Lions. This file fixes the interfaces: the order on bilinear forms, the
second-order jets and their closures, and the exact statement of the theorem of
sums that the comparison argument consumes.

The theorem of sums is stated here as a proposition, `TheoremOfSums`, and is
proved later. Stating it first and proving the comparison principle from it
fixes every interface before the deep analysis is begun.

## The order

Every operator in the predicates sees a bilinear form only through its
quadratic form, so the order used is the quadratic-form order:
`X ≤ Y` means `X(v,v) ≤ Y(v,v)` for every `v`. No symmetry is assumed.

## Jets

A superjet of `u` at `x` is a pair `(q, X)` such that, for every `η > 0`, near
`x`,

  `u y ≤ u x + ⟪q, y - x⟫ + ½ X(y - x, y - x) + η ‖y - x‖²`.

This is the little-o form of the usual definition, quantified so that the
polynomial on the right is a valid test function for each `η`.

## Closed jets

The closure is taken with the forms converging in operator norm, explicitly.
Convergence in the topology of the space of continuous linear maps is the same
thing mathematically, but turning it into norm convergence makes the
elaborator unify two topologies on that space and time out, the obstruction
recorded among the findings on derivative representations. Stating the norm
convergence directly keeps every downstream argument in normed terms.

## The statement

For `u` upper and `v` lower semicontinuous and bounded, if
`u x - v y - ‖x - y‖⁴ / (4α)` has a local maximum at `(x̂, ŷ)`, there are forms
`X ≤ Y` with `(q, X)` in the closed superjet of `u` at `x̂` and `(q, Y)` in the
closed subjet of `v` at `ŷ`, where `q = (‖x̂ - ŷ‖² / α) (x̂ - ŷ)` is the gradient
of the penalty; and if `x̂ = ŷ`, moreover `X ≤ 0 ≤ Y`.

This follows from the theorem of sums of [CIL92, Thm 3.2] for the penalty
`φ(x,y) = ‖x - y‖⁴/(4α)`. There the matrices satisfy
`diag(X, -Y) ≤ A + ε A²` with `A = D²φ(x̂, ŷ)`. Since `φ` depends on `x - y`
only, `A` annihilates every direction `(v, v)`, which gives `X ≤ Y`; and at
`x̂ = ŷ` the quartic has vanishing Hessian, so `A = 0` and `X ≤ 0 ≤ Y`.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- The bilinear forms on the space. -/
abbrev Bilin (d : ℕ) := EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ

/-- **The quadratic-form order.** -/
def QuadLE (X Y : Bilin d) : Prop := ∀ v : EuclSpace d, (X v) v ≤ (Y v) v

theorem QuadLE.refl (X : Bilin d) : QuadLE X X := fun _ => le_refl _

theorem QuadLE.trans {X Y Z : Bilin d} (h1 : QuadLE X Y) (h2 : QuadLE Y Z) :
    QuadLE X Z := fun v => le_trans (h1 v) (h2 v)

/-- **The second-order superjet.** -/
def SuperJet (u : EuclSpace d → ℝ) (x : EuclSpace d) :
    Set (EuclSpace d × Bilin d) :=
  {qX | ∀ η > 0, ∀ᶠ y in 𝓝 x,
    u y ≤ u x + inner ℝ qX.1 (y - x)
      + (1 / 2) * (qX.2 (y - x)) (y - x) + η * ‖y - x‖ ^ 2}

/-- **The second-order subjet.** -/
def SubJet (u : EuclSpace d → ℝ) (x : EuclSpace d) :
    Set (EuclSpace d × Bilin d) :=
  {qX | ∀ η > 0, ∀ᶠ y in 𝓝 x,
    u x + inner ℝ qX.1 (y - x)
      + (1 / 2) * (qX.2 (y - x)) (y - x) - η * ‖y - x‖ ^ 2 ≤ u y}

/-- **The closed superjet**: limits of superjets at nearby points along which
the function converges. -/
def ClSuperJet (u : EuclSpace d → ℝ) (x : EuclSpace d) :
    Set (EuclSpace d × Bilin d) :=
  {qX | ∃ xs : ℕ → EuclSpace d, ∃ qs : ℕ → EuclSpace d, ∃ Xs : ℕ → Bilin d,
    (∀ n, (qs n, Xs n) ∈ SuperJet u (xs n)) ∧
    Tendsto xs atTop (𝓝 x) ∧
    Tendsto (fun n => u (xs n)) atTop (𝓝 (u x)) ∧
    Tendsto qs atTop (𝓝 qX.1) ∧
    Tendsto (fun n => ‖Xs n - qX.2‖) atTop (𝓝 0)}

/-- **The closed subjet.** -/
def ClSubJet (u : EuclSpace d → ℝ) (x : EuclSpace d) :
    Set (EuclSpace d × Bilin d) :=
  {qX | ∃ xs : ℕ → EuclSpace d, ∃ qs : ℕ → EuclSpace d, ∃ Xs : ℕ → Bilin d,
    (∀ n, (qs n, Xs n) ∈ SubJet u (xs n)) ∧
    Tendsto xs atTop (𝓝 x) ∧
    Tendsto (fun n => u (xs n)) atTop (𝓝 (u x)) ∧
    Tendsto qs atTop (𝓝 qX.1) ∧
    Tendsto (fun n => ‖Xs n - qX.2‖) atTop (𝓝 0)}

/-- A superjet is a closed superjet, by constant sequences. -/
theorem superJet_subset_cl (u : EuclSpace d → ℝ) (x : EuclSpace d) :
    SuperJet u x ⊆ ClSuperJet u x := by
  intro qX h
  refine ⟨fun _ => x, fun _ => qX.1, fun _ => qX.2, fun _ => h,
    tendsto_const_nhds, tendsto_const_nhds, tendsto_const_nhds, ?_⟩
  simp

/-- A subjet is a closed subjet, by constant sequences. -/
theorem subJet_subset_cl (u : EuclSpace d → ℝ) (x : EuclSpace d) :
    SubJet u x ⊆ ClSubJet u x := by
  intro qX h
  refine ⟨fun _ => x, fun _ => qX.1, fun _ => qX.2, fun _ => h,
    tendsto_const_nhds, tendsto_const_nhds, tendsto_const_nhds, ?_⟩
  simp

/-- The gradient of the quartic penalty. -/
def penaltyGrad (α : ℝ) (x y : EuclSpace d) : EuclSpace d :=
  (‖x - y‖ ^ 2 / α) • (x - y)

/-- **The theorem of sums, in the form the comparison argument consumes.**
Stated as a proposition, and proved separately. -/
def TheoremOfSums (d : ℕ) : Prop :=
  ∀ (u v : EuclSpace d → ℝ), UpperSemicontinuous u → LowerSemicontinuous v →
    BddAbove (range u) → BddBelow (range v) →
    ∀ α : ℝ, 0 < α → ∀ xh yh : EuclSpace d,
      IsLocalMax
        (fun z : EuclSpace d × EuclSpace d =>
          u z.1 - v z.2 - ‖z.1 - z.2‖ ^ 4 / (4 * α)) (xh, yh) →
      ∃ X Y : Bilin d,
        (penaltyGrad α xh yh, X) ∈ ClSuperJet u xh ∧
        (penaltyGrad α xh yh, Y) ∈ ClSubJet v yh ∧
        QuadLE X Y ∧
        (xh = yh → QuadLE X 0 ∧ QuadLE 0 Y)

/-- At coincident points the penalty gradient vanishes. -/
theorem penaltyGrad_self (α : ℝ) (x : EuclSpace d) : penaltyGrad α x x = 0 := by
  simp [penaltyGrad]

end

end PLaplacian
