/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Plaplacian.UniformConvergence

@[expose] public section

/-!
# Index selection for the uniform convergence argument

The proof of uniform convergence in Luiro--Parviainen--Saksman
(*On the existence and uniqueness of `p`-harmonious functions*, Differential
Integral Equations 27 (2014), Thm. 2.1) chooses three indices in sequence:

* `k` with `sup (u - u_k) ≤ M + δ`;
* a point `x₀` nearly attaining `sup (u - u_{k+1})`;
* `ℓ > k` with `u x₀ - u_{ℓ+1} x₀ < δ`.

This file supplies each selection, and the object `M` they refer to. Everything
here is stated for an abstract monotone approximating sequence
`w : ℕ → EuclSpace d → ℝ` rather than for `iter` specifically, since the
hypotheses are exactly what `Plaplacian.Iteration` provides and the argument
uses nothing else.

## Main results

- `deficitSup`: the supremum of `u - w` over a set.
- `exists_deficitLimit`: the deficit sups decrease and converge, giving `M`.
- `exists_index_le`, `deficit_le_of_index`: selection of `k`, and its
  pointwise form.
- `exists_point_near`: selection of `x₀`.
- `eventually_deficit_lt`, `exists_late_index`: selection of `ℓ`.
-/

open MeasureTheory Metric Set Filter

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-! ### The limit `M` -/

/-- The supremum of the deficit `u - w` over a set. -/
def deficitSup (S : Set (EuclSpace d)) (u : EuclSpace d → ℝ)
    (w : EuclSpace d → ℝ) : ℝ :=
  sSup ((fun x => u x - w x) '' S)

lemma bddAbove_deficit {S : Set (EuclSpace d)} {u w : EuclSpace d → ℝ}
    {C : ℝ} (hC : ∀ x, |u x - w x| ≤ C) :
    BddAbove ((fun x => u x - w x) '' S) :=
  ⟨C, by rintro a ⟨x, -, rfl⟩; exact (abs_le.1 (hC x)).2⟩

lemma deficitSup_nonneg {S : Set (EuclSpace d)} (hS : S.Nonempty)
    {u w : EuclSpace d → ℝ} {C : ℝ} (hC : ∀ x, |u x - w x| ≤ C)
    (hnn : ∀ x, 0 ≤ u x - w x) :
    0 ≤ deficitSup S u w := by
  obtain ⟨x₀, hx₀⟩ := hS
  exact le_trans (hnn x₀) (le_csSup (bddAbove_deficit hC) ⟨x₀, hx₀, rfl⟩)

/-- The deficit sups decrease, because the approximants increase. -/
lemma deficitSup_antitone {S : Set (EuclSpace d)} (hS : S.Nonempty)
    {u : EuclSpace d → ℝ} {w : ℕ → EuclSpace d → ℝ} {C : ℝ}
    (hC : ∀ j x, |u x - w j x| ≤ C)
    (hmono : ∀ j x, w j x ≤ w (j + 1) x) :
    Antitone (fun j => deficitSup S u (w j)) := by
  refine antitone_nat_of_succ_le fun j => ?_
  refine csSup_le (hS.image _) ?_
  rintro a ⟨x, hx, rfl⟩
  have h1 : u x - w (j + 1) x ≤ u x - w j x := by linarith [hmono j x]
  exact le_trans h1 (le_csSup (bddAbove_deficit (hC j)) ⟨x, hx, rfl⟩)

/-- **The limit `M` exists**, as the limit of a decreasing bounded sequence. -/
theorem exists_deficitLimit {S : Set (EuclSpace d)} (hS : S.Nonempty)
    {u : EuclSpace d → ℝ} {w : ℕ → EuclSpace d → ℝ} {C : ℝ}
    (hC : ∀ j x, |u x - w j x| ≤ C)
    (hnn : ∀ j x, 0 ≤ u x - w j x)
    (hmono : ∀ j x, w j x ≤ w (j + 1) x) :
    ∃ M : ℝ, Tendsto (fun j => deficitSup S u (w j)) atTop (nhds M) := by
  have hbdd : BddBelow (Set.range fun j => deficitSup S u (w j)) := by
    refine ⟨0, ?_⟩
    rintro a ⟨j, rfl⟩
    exact deficitSup_nonneg hS (hC j) (hnn j)
  exact ⟨_, tendsto_atTop_ciInf (deficitSup_antitone hS hC hmono) hbdd⟩

/-! ### Selection of `k` -/

/-- LPS's (2.6). -/
theorem exists_index_le {S : Set (EuclSpace d)} {u : EuclSpace d → ℝ}
    {w : ℕ → EuclSpace d → ℝ} {M δ : ℝ} (hδ : 0 < δ)
    (hlim : Tendsto (fun j => deficitSup S u (w j)) atTop (nhds M)) :
    ∃ k, deficitSup S u (w k) ≤ M + δ := by
  have h := hlim.eventually (eventually_le_nhds (by linarith : M < M + δ))
  obtain ⟨k, hk⟩ := h.exists
  exact ⟨k, hk⟩

/-- Pointwise form of (2.6). -/
theorem deficit_le_of_index {S : Set (EuclSpace d)} {u : EuclSpace d → ℝ}
    {w : ℕ → EuclSpace d → ℝ} {M δ : ℝ} {k : ℕ} {C : ℝ}
    (hC : ∀ x, |u x - w k x| ≤ C)
    (hk : deficitSup S u (w k) ≤ M + δ)
    {x : EuclSpace d} (hx : x ∈ S) :
    u x - w k x ≤ M + δ :=
  le_trans (le_csSup (bddAbove_deficit hC) ⟨x, hx, rfl⟩) hk

/-! ### Selection of `x₀` -/

/-- A point nearly attaining the deficit sup. Boundedness is not needed:
`exists_lt_of_lt_csSup` requires only nonemptiness. -/
theorem exists_point_near {S : Set (EuclSpace d)} (hS : S.Nonempty)
    {u : EuclSpace d → ℝ} {w : EuclSpace d → ℝ} {δ : ℝ} (hδ : 0 < δ) :
    ∃ x₀ ∈ S, deficitSup S u w - δ ≤ u x₀ - w x₀ := by
  obtain ⟨a, ha, hlt⟩ := exists_lt_of_lt_csSup (hS.image _)
    (show deficitSup S u w - δ < deficitSup S u w by linarith)
  obtain ⟨x₀, hx₀S, rfl⟩ := ha
  exact ⟨x₀, hx₀S, hlt.le⟩

/-! ### Selection of `ℓ` -/

theorem eventually_deficit_lt {u : EuclSpace d → ℝ}
    {w : ℕ → EuclSpace d → ℝ} {x₀ : EuclSpace d} {δ : ℝ} (hδ : 0 < δ)
    (hconv : Tendsto (fun j => w j x₀) atTop (nhds (u x₀))) :
    ∀ᶠ j in atTop, u x₀ - w j x₀ < δ := by
  have hd : Tendsto (fun j => u x₀ - w j x₀) atTop (nhds 0) := by
    have := hconv.const_sub (u x₀)
    simpa using this
  exact hd.eventually (eventually_lt_nhds hδ)

/-- LPS's choice of `ℓ > k`. -/
theorem exists_late_index {u : EuclSpace d → ℝ} {w : ℕ → EuclSpace d → ℝ}
    {x₀ : EuclSpace d} {δ : ℝ} (hδ : 0 < δ)
    (hconv : Tendsto (fun j => w j x₀) atTop (nhds (u x₀))) (k : ℕ) :
    ∃ ℓ, k < ℓ ∧ u x₀ - w (ℓ + 1) x₀ < δ := by
  have h := eventually_deficit_lt hδ hconv
  obtain ⟨N, hN⟩ := (h.and (eventually_gt_atTop k)).exists_forall_of_atTop
  refine ⟨N, (hN N le_rfl).2, ?_⟩
  exact (hN (N + 1) (Nat.le_succ N)).1

end PLaplacian
