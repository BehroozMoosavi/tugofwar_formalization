/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Plaplacian.Comparison
public import Plaplacian.ExtremeValues

@[expose] public section

/-!
# Invariance of the admissible class

The existence proof iterates `T_ε`, so the admissible class of
Definition `BddMeas` --- bounded and Borel measurable --- must be preserved by
the operator. This file proves that.

## Why this is the pay-off of the open-ball choice

Measurability of the two extreme-value terms is `Plaplacian.Measurability`, and
holds only because the balls in `tugOfWarOp` are open: over closed balls the
supremum operator does not preserve Borel measurability, so the iteration below
could not even be stated. Measurability of the *average* term is proved here,
by rewriting the integral over the moving ball as an integral over a fixed ball
of a translated integrand (`setIntegral_ball_translate`), which turns the
question into measurability of a parameter integral and is discharged by
`MeasureTheory.StronglyMeasurable.integral_prod_right`.

Preservation of the bound is a convexity argument: each of `sup`, `inf` and the
average lies in `[-C, C]`, the weights are nonnegative, and `α + β = 1`.

## Main results

- `measurable_setAverage_ball`: the average over a moving ball is measurable.
- `abs_tugOfWarOp_le`: the operator preserves any pointwise bound.
- `BddMeas.tugOfWarOp`: **the admissible class is invariant.**
-/

open MeasureTheory Metric Set

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-! ### Measurability of the average term -/

lemma measurable_translate {v : EuclSpace d → ℝ} (hv : Measurable v) :
    Measurable (fun q : EuclSpace d × EuclSpace d => v (q.1 + q.2)) :=
  hv.comp (measurable_fst.add measurable_snd)

/-- The integral over a moving ball is measurable in the centre. -/
lemma measurable_setIntegral_ball {v : EuclSpace d → ℝ} (hv : Measurable v)
    (ε : ℝ) :
    Measurable (fun x : EuclSpace d => ∫ y in ball x ε, v y) := by
  have hrw : (fun x : EuclSpace d => ∫ y in ball x ε, v y)
      = fun x : EuclSpace d =>
          ∫ z : EuclSpace d, (ball (0 : EuclSpace d) ε).indicator
            (fun z => v (x + z)) z := by
    funext x
    rw [setIntegral_ball_translate v x ε,
        ← MeasureTheory.integral_indicator measurableSet_ball]
  rw [hrw]
  have hjoint : StronglyMeasurable
      (Function.uncurry fun (x z : EuclSpace d) =>
        (ball (0 : EuclSpace d) ε).indicator (fun w => v (x + w)) z) := by
    refine Measurable.stronglyMeasurable ?_
    have hset : MeasurableSet
        {q : EuclSpace d × EuclSpace d | q.2 ∈ ball (0 : EuclSpace d) ε} :=
      measurable_snd measurableSet_ball
    have heq : (Function.uncurry fun (x z : EuclSpace d) =>
        (ball (0 : EuclSpace d) ε).indicator (fun w => v (x + w)) z)
        = {q : EuclSpace d × EuclSpace d |
            q.2 ∈ ball (0 : EuclSpace d) ε}.indicator
            (fun q => v (q.1 + q.2)) := by
      funext q
      simp only [Function.uncurry]
      rfl
    rw [heq]
    exact (measurable_translate hv).indicator hset
  exact (StronglyMeasurable.integral_prod_right hjoint).measurable

/-- **The average over a moving ball is measurable.** The normalising factor is
constant in the centre, by `volumeReal_ball_center`. -/
lemma measurable_setAverage_ball {v : EuclSpace d → ℝ} (hv : Measurable v)
    (ε : ℝ) :
    Measurable (fun x : EuclSpace d => ⨍ y in ball x ε, v y) := by
  have hrw : (fun x : EuclSpace d => ⨍ y in ball x ε, v y)
      = fun x : EuclSpace d =>
          (volume.real (ball (0 : EuclSpace d) ε))⁻¹
            * ∫ y in ball x ε, v y := by
    funext x
    rw [MeasureTheory.setAverage_eq, volumeReal_ball_center x ε, smul_eq_mul]
  rw [hrw]
  exact (measurable_setIntegral_ball hv ε).const_mul _

/-! ### Preservation of the bound -/

lemma sSup_ball_le {v : EuclSpace d → ℝ} {C : ℝ} (hC : ∀ y, |v y| ≤ C)
    (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    sSup (v '' ball x ε) ≤ C := by
  refine csSup_le ⟨v x, x, mem_ball_self hε, rfl⟩ ?_
  rintro a ⟨y, -, rfl⟩
  exact (abs_le.1 (hC y)).2

lemma le_sInf_ball {v : EuclSpace d → ℝ} {C : ℝ} (hC : ∀ y, |v y| ≤ C)
    (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    -C ≤ sInf (v '' ball x ε) := by
  refine le_csInf ⟨v x, x, mem_ball_self hε, rfl⟩ ?_
  rintro a ⟨y, -, rfl⟩
  exact (abs_le.1 (hC y)).1

lemma sInf_ball_le {v : EuclSpace d → ℝ} {C : ℝ} (hC : ∀ y, |v y| ≤ C)
    (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    sInf (v '' ball x ε) ≤ C := by
  have hbdd : BddBelow (v '' ball x ε) :=
    ⟨-C, by rintro a ⟨y, -, rfl⟩; exact (abs_le.1 (hC y)).1⟩
  exact le_trans (csInf_le hbdd ⟨x, mem_ball_self hε, rfl⟩) (abs_le.1 (hC x)).2

lemma neg_le_sSup_ball {v : EuclSpace d → ℝ} {C : ℝ} (hC : ∀ y, |v y| ≤ C)
    (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    -C ≤ sSup (v '' ball x ε) := by
  have hbdd : BddAbove (v '' ball x ε) :=
    ⟨C, by rintro a ⟨y, -, rfl⟩; exact (abs_le.1 (hC y)).2⟩
  exact le_trans (abs_le.1 (hC x)).1 (le_csSup hbdd ⟨x, mem_ball_self hε, rfl⟩)

lemma abs_setAverage_ball_le {v : EuclSpace d → ℝ} (hv : BddMeas v) {C : ℝ}
    (hC : ∀ y, |v y| ≤ C) (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    |⨍ y in ball x ε, v y| ≤ C := by
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · have h0 : (⨍ _y in ball x ε, (-C)) = -C := setAverage_const_ball (-C) x hε
    rw [← h0]
    exact setAverage_mono_ball x integrableOn_const (hv.integrableOn_ball x ε)
      (fun y => (abs_le.1 (hC y)).1)
  · have h0 : (⨍ _y in ball x ε, C) = C := setAverage_const_ball C x hε
    rw [← h0]
    exact setAverage_mono_ball x (hv.integrableOn_ball x ε) integrableOn_const
      (fun y => (abs_le.1 (hC y)).2)

/-- **The operator preserves any pointwise bound**, by convexity of the
weights. -/
theorem abs_tugOfWarOp_le (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ))
    {v : EuclSpace d → ℝ} (hv : BddMeas v) {C : ℝ} (hC : ∀ y, |v y| ≤ C)
    (x : EuclSpace d) :
    |tugOfWarOp p ε v x| ≤ C := by
  have hα : 0 ≤ (p - 2) / (p + (d : ℝ)) := div_nonneg (by linarith) hpd.le
  have hβ : 0 ≤ ((d : ℝ) + 2) / (p + (d : ℝ)) := by positivity
  have hab : (p - 2) / (p + (d : ℝ)) + ((d : ℝ) + 2) / (p + (d : ℝ)) = 1 :=
    alpha_add_beta p hpd
  have hs1 := sSup_ball_le hC x hε
  have hs2 := neg_le_sSup_ball hC x hε
  have hi1 := sInf_ball_le hC x hε
  have hi2 := le_sInf_ball hC x hε
  have ha := abs_le.1 (abs_setAverage_ball_le hv hC x hε)
  unfold PLaplacian.tugOfWarOp
  rw [abs_le]
  constructor <;> nlinarith [hs1, hs2, hi1, hi2, ha.1, ha.2, hα, hβ, hab]

/-! ### Invariance -/

/-- **The admissible class is invariant under the step operator.** This is what
makes the monotone iteration of the existence proof well defined. -/
theorem BddMeas.tugOfWarOp (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ))
    {v : EuclSpace d → ℝ} (hv : BddMeas v) :
    BddMeas (tugOfWarOp p ε v) := by
  obtain ⟨C, hC⟩ := hv.bound
  refine ⟨?_, ⟨C, fun x => abs_tugOfWarOp_le p ε hp hε hpd hv hC x⟩⟩
  unfold PLaplacian.tugOfWarOp
  have h1 : Measurable (fun x : EuclSpace d => sSup (v '' ball x ε)) :=
    measurable_sSup_ball v hε ⟨C, hC⟩
  have h2 : Measurable (fun x : EuclSpace d => sInf (v '' ball x ε)) :=
    measurable_sInf_ball v hε ⟨C, hC⟩
  have h3 : Measurable (fun x : EuclSpace d => ⨍ y in ball x ε, v y) :=
    measurable_setAverage_ball hv.meas ε
  exact ((h1.add h2).const_mul _).add (h3.const_mul _)

end PLaplacian
