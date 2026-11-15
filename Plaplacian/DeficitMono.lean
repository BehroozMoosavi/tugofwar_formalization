/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Plaplacian.UniformLimit

@[expose] public section

/-!
# Monotonicity facts for the deficit

Auxiliary monotonicity results needed to instantiate the abstract uniform
convergence theorem of Plaplacian.UniformLimit at the Perron iteration. The
chained estimate of Luiro-Parviainen-Saksman compares the iterates at two
indices and then replaces the later one by the limit, which requires
monotonicity of the supremum and of the average in the numerator, and the fact
that every iterate lies below the pointwise supremum.

## Main results

- sSup_diff_mono, setAverage_diff_mono
- iter_le_of_le, iter_le_iterLimit
- deficit_nonneg, abs_deficit_le
-/

open MeasureTheory Metric Set Filter

noncomputable section

variable {d : ℕ}

namespace PLaplacian





/-- If `w ≤ u` pointwise then the sup of `w - v` is at most the sup of
`u - v`. Used to replace `u_ℓ` by `u` in the chained estimate. -/
theorem sSup_diff_mono {S : Set (EuclSpace d)} (hS : S.Nonempty)
    {u w v : EuclSpace d → ℝ} (hwu : ∀ x, w x ≤ u x)
    {C : ℝ} (hC : ∀ x, |u x - v x| ≤ C) :
    sSup ((fun x => w x - v x) '' S) ≤ sSup ((fun x => u x - v x) '' S) := by
  refine csSup_le (hS.image _) ?_
  rintro a ⟨x, hx, rfl⟩
  have h1 : w x - v x ≤ u x - v x := by linarith [hwu x]
  exact le_trans h1 (le_csSup (bddAbove_deficit hC) ⟨x, hx, rfl⟩)

/-- Same for the average over a ball. -/
theorem setAverage_diff_mono {u w v : EuclSpace d → ℝ}
    (hwu : ∀ x, w x ≤ u x) (x : EuclSpace d) {ε : ℝ}
    (hwv : MeasureTheory.IntegrableOn (fun y => w y - v y) (ball x ε))
    (huv : MeasureTheory.IntegrableOn (fun y => u y - v y) (ball x ε)) :
    (⨍ y in ball x ε, (w y - v y)) ≤ ⨍ y in ball x ε, (u y - v y) :=
  setAverage_mono_ball x hwv huv (fun y => by linarith [hwu y])

/-- Monotonicity of the iteration in the index. -/
theorem iter_le_of_le (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ))
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀)
    (hstep : ∀ x, u₀ x ≤ tugOfWarOp p ε u₀ x) {i j : ℕ} (hij : i ≤ j) :
    ∀ x, iter p ε u₀ i x ≤ iter p ε u₀ j x := by
  intro x
  exact monotone_iter p ε hp hε hd hpd hu₀ hstep x hij





/-- Each iterate is below the limit, since the limit is the supremum. -/
theorem iter_le_iterLimit (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (_hd : 0 < d)
    (hpd : 0 < p + (d : ℝ))
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C)
    (_hstep : ∀ x, u₀ x ≤ tugOfWarOp p ε u₀ x) (j : ℕ) (x : EuclSpace d) :
    iter p ε u₀ j x ≤ iterLimit p ε u₀ x := by
  unfold iterLimit
  refine le_ciSup (f := fun i => iter p ε u₀ i x) ?_ j
  refine ⟨C, ?_⟩
  rintro a ⟨i, rfl⟩
  exact (abs_le.1 (abs_iter_le p ε hp hε hpd hu₀ hC i x)).2

/-- The deficit is nonnegative. -/
theorem deficit_nonneg (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ))
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C)
    (hstep : ∀ x, u₀ x ≤ tugOfWarOp p ε u₀ x) (j : ℕ) (x : EuclSpace d) :
    0 ≤ iterLimit p ε u₀ x - iter p ε u₀ j x := by
  have := iter_le_iterLimit p ε hp hε hd hpd hu₀ hC hstep j x
  linarith

/-- The deficit is bounded by `2C`. -/
theorem abs_deficit_le (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ))
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C)
    (hstep : ∀ x, u₀ x ≤ tugOfWarOp p ε u₀ x) (j : ℕ) (x : EuclSpace d) :
    |iterLimit p ε u₀ x - iter p ε u₀ j x| ≤ 2 * C := by
  have hlo := (abs_le.1 (abs_iter_le p ε hp hε hpd hu₀ hC j x)).1
  have hhi := (abs_le.1 (abs_iter_le p ε hp hε hpd hu₀ hC j x)).2
  have hLlo : -C ≤ iterLimit p ε u₀ x := by
    have := iter_le_iterLimit p ε hp hε hd hpd hu₀ hC hstep 0 x
    simp only [iter_zero] at this
    linarith [(abs_le.1 (hC x)).1]
  have hLhi : iterLimit p ε u₀ x ≤ C := by
    unfold iterLimit
    refine ciSup_le fun i => ?_
    exact (abs_le.1 (abs_iter_le p ε hp hε hpd hu₀ hC i x)).2
  rw [abs_le]
  constructor <;> linarith

end PLaplacian

end
