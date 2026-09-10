/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Plaplacian.Invariance

/-!
# The Perron iteration

Existence of `p`-harmonious functions is obtained in
Luiro--Parviainen--Saksman (*On the existence and uniqueness of `p`-harmonious
functions*, Differential Integral Equations 27 (2014), Thm. 2.1) by iterating
the step operator from a subsolution. This file sets up the iteration and
proves the elementary properties: every iterate is admissible, the sequence is
monotone increasing, it is uniformly bounded, and it converges pointwise.

`bddMeas_iter` is where `Plaplacian.Invariance` is used, and hence where the
open-ball choice in `tugOfWarOp` becomes indispensable: for closed balls the
iterates need not be measurable and the sequence is not even well defined
within the admissible class.

## Main results

- `iter`: the iteration `u₀`, `T_ε u₀`, `T_ε² u₀`, ...
- `bddMeas_iter`: every iterate is admissible.
- `iter_mono`, `monotone_iter`: monotone increasing from a subsolution.
- `abs_iter_le`: uniformly bounded by the bound on `u₀`.
- `tendsto_iter`: **pointwise convergence.**

## TODO

Uniform convergence, which is the substantive step of the LPS argument and
uses `β > 0`; and verification that the limit satisfies the dynamic programming
principle, which needs to pass `T_ε` through the limit.
-/

open MeasureTheory Metric Set Filter

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-- The Perron iteration: `u₀` given, `u_{j+1} = T_ε u_j`. -/
def iter (p ε : ℝ) (u₀ : EuclSpace d → ℝ) : ℕ → (EuclSpace d → ℝ)
  | 0 => u₀
  | (j+1) => tugOfWarOp p ε (iter p ε u₀ j)

@[simp] lemma iter_zero (p ε : ℝ) (u₀ : EuclSpace d → ℝ) :
    iter p ε u₀ 0 = u₀ := rfl

@[simp] lemma iter_succ (p ε : ℝ) (u₀ : EuclSpace d → ℝ) (j : ℕ) :
    iter p ε u₀ (j+1) = tugOfWarOp p ε (iter p ε u₀ j) := rfl

/-- Every iterate is admissible. Uses `Plaplacian.Invariance`. -/
theorem bddMeas_iter (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ))
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) (j : ℕ) :
    BddMeas (iter p ε u₀ j) := by
  induction j with
  | zero => exact hu₀
  | succ n ih => exact BddMeas.tugOfWarOp p ε hp hε hpd ih

/-- From a subsolution the iteration increases, by monotonicity of `T_ε`. -/
theorem iter_mono (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ))
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀)
    (hstep : ∀ x, u₀ x ≤ tugOfWarOp p ε u₀ x) (j : ℕ) :
    ∀ x, iter p ε u₀ j x ≤ iter p ε u₀ (j+1) x := by
  induction j with
  | zero => exact hstep
  | succ n ih =>
      intro x
      exact tugOfWarOp_monotone p ε hp hd hε
        (bddMeas_iter p ε hp hε hpd hu₀ n)
        (bddMeas_iter p ε hp hε hpd hu₀ (n+1)) ih x

/-- The bound on `u₀` propagates to the whole sequence. -/
theorem abs_iter_le (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ))
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C) (j : ℕ) :
    ∀ x, |iter p ε u₀ j x| ≤ C := by
  induction j with
  | zero => exact hC
  | succ n ih =>
      intro x
      exact abs_tugOfWarOp_le p ε hp hε hpd
        (bddMeas_iter p ε hp hε hpd hu₀ n) ih x

theorem monotone_iter (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ))
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀)
    (hstep : ∀ x, u₀ x ≤ tugOfWarOp p ε u₀ x) (x : EuclSpace d) :
    Monotone (fun j => iter p ε u₀ j x) :=
  monotone_nat_of_le_succ fun n =>
    iter_mono p ε hp hε hd hpd hu₀ hstep n x

/-- **Pointwise convergence** to the pointwise supremum. -/
theorem tendsto_iter (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ))
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C)
    (hstep : ∀ x, u₀ x ≤ tugOfWarOp p ε u₀ x) (x : EuclSpace d) :
    ∃ L : ℝ, Tendsto (fun j => iter p ε u₀ j x) atTop (nhds L) := by
  have hbdd : BddAbove (Set.range fun j => iter p ε u₀ j x) := by
    refine ⟨C, ?_⟩
    rintro a ⟨j, rfl⟩
    exact (abs_le.1 (abs_iter_le p ε hp hε hpd hu₀ hC j x)).2
  exact ⟨_, tendsto_atTop_ciSup
    (monotone_iter p ε hp hε hd hpd hu₀ hstep x) hbdd⟩

/-- The limit function, defined as the pointwise supremum. -/
def iterLimit (p ε : ℝ) (u₀ : EuclSpace d → ℝ) (x : EuclSpace d) : ℝ :=
  ⨆ j, iter p ε u₀ j x

theorem tendsto_iterLimit (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ))
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C)
    (hstep : ∀ x, u₀ x ≤ tugOfWarOp p ε u₀ x) (x : EuclSpace d) :
    Tendsto (fun j => iter p ε u₀ j x) atTop (nhds (iterLimit p ε u₀ x)) := by
  have hbdd : BddAbove (Set.range fun j => iter p ε u₀ j x) := by
    refine ⟨C, ?_⟩
    rintro a ⟨j, rfl⟩
    exact (abs_le.1 (abs_iter_le p ε hp hε hpd hu₀ hC j x)).2
  exact tendsto_atTop_ciSup
    (monotone_iter p ε hp hε hd hpd hu₀ hstep x) hbdd

end PLaplacian
