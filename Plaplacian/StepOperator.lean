/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Plaplacian.Average

/-!
# The tug-of-war step operator

For `ε > 0` and `v` bounded and measurable, the step operator of the
`ε`-step tug-of-war game with noise is

  `T_ε v (x) = (α/2) (sup_{closedBall x ε} v + inf_{closedBall x ε} v)
                 + β ⨍_{ball x ε} v`

with weights `α = (p-2)/(p+d)` and `β = (d+2)/(p+d)`, so that `α + β = 1`.
The dynamic programming principle `u_ε = T_ε u_ε` on the domain, with `u_ε = F`
on the boundary strip, is taken as the *definition* of the discrete problem.

## The hypothesis class

Functions are plain `EuclSpace d → ℝ` carrying the predicate `BddMeas`
(measurable and bounded). Three points motivate this:

* `BoundedContinuousFunction` is *not* usable: `T_ε` does not preserve
  continuity, since `sup`/`inf` over a ball need not, so `u_ε` is not
  continuous.
* Boundedness alone is not enough either: it does not give integrability, which
  `setAverage_mono_ball` requires. Measurability must be carried explicitly.
* Bundling the two as a structure rather than passing loose hypotheses matters
  in practice, because every lemma downstream needs both.

## Restriction to `2 ≤ p`

`tugOfWarOp_monotone` assumes `2 ≤ p`, and this is essential rather than
incidental: for `1 < p < 2` the weight `α` is negative, so the
`sup + inf` term is *anti*-monotone and the operator as written above is not
monotone. Treating `1 < p < 2` requires the regrouped formulation in which the
roles of `sup` and `inf` are exchanged, and is not done here.

## Main results

- `BddMeas`: the hypothesis class, with projections for integrability on a ball
  and for `BddAbove`/`BddBelow` of the image.
- `sSup_image_mono`, `sInf_image_mono`: monotonicity of the extreme values under
  a pointwise bound.
- `tugOfWarOp`: the step operator.
- `alpha_add_beta`: the weights sum to one.
- `tugOfWarOp_monotone`: monotonicity of the operator, for `2 ≤ p`.

## TODO

- Nonexpansiveness in the sup norm.
- The discrete comparison principle, via the strict concave perturbation
  `ψ x = R ^ 2 - ‖x‖ ^ 2`; note that `T_ε` is nonexpansive but *not*
  contractive, so uniqueness does not follow from a fixed point theorem.
- Existence and uniqueness of `p`-harmonious functions.
-/

open MeasureTheory Metric Set

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-! ### The hypothesis class -/

/-- Bounded and measurable: the class on which the step operator is defined.
See the module docstring for why neither boundedness alone nor continuity is
the right condition. -/
structure BddMeas (v : EuclSpace d → ℝ) : Prop where
  meas : Measurable v
  bound : ∃ C, ∀ y, |v y| ≤ C

/-- A bounded measurable function is integrable on a ball, which is what the
average term requires. -/
lemma BddMeas.integrableOn_ball {v : EuclSpace d → ℝ} (hv : BddMeas v)
    (x : EuclSpace d) (ε : ℝ) : IntegrableOn v (ball x ε) := by
  obtain ⟨C, hC⟩ := hv.bound
  have hconst : IntegrableOn (fun _ : EuclSpace d => C) (ball x ε) :=
    integrableOn_const
  exact hconst.mono' hv.meas.aestronglyMeasurable.restrict
    (Filter.Eventually.of_forall fun y => by simpa using hC y)

/-- Without this the `sSup` in the operator is a junk value. -/
lemma BddMeas.bddAbove_image {v : EuclSpace d → ℝ} (hv : BddMeas v)
    (x : EuclSpace d) (ε : ℝ) : BddAbove (v '' closedBall x ε) := by
  obtain ⟨C, hC⟩ := hv.bound
  exact ⟨C, by rintro a ⟨y, -, rfl⟩; exact (abs_le.1 (hC y)).2⟩

/-- Without this the `sInf` in the operator is a junk value. -/
lemma BddMeas.bddBelow_image {v : EuclSpace d → ℝ} (hv : BddMeas v)
    (x : EuclSpace d) (ε : ℝ) : BddBelow (v '' closedBall x ε) := by
  obtain ⟨C, hC⟩ := hv.bound
  exact ⟨-C, by rintro a ⟨y, -, rfl⟩; exact (abs_le.1 (hC y)).1⟩

lemma nonempty_closedBall (x : EuclSpace d) {ε : ℝ} (hε : 0 ≤ ε) :
    (closedBall x ε : Set (EuclSpace d)).Nonempty :=
  ⟨x, mem_closedBall_self hε⟩

/-! ### Monotonicity of the extreme values -/

/-- Monotonicity of `sSup` over an image under a pointwise bound. -/
lemma sSup_image_mono {u v : EuclSpace d → ℝ} {s : Set (EuclSpace d)}
    (hs : s.Nonempty) (hv : BddAbove (v '' s)) (h : ∀ y, u y ≤ v y) :
    sSup (u '' s) ≤ sSup (v '' s) := by
  refine csSup_le (hs.image u) ?_
  rintro a ⟨y, hy, rfl⟩
  exact le_trans (h y) (le_csSup hv ⟨y, hy, rfl⟩)

/-- Monotonicity of `sInf` over an image under a pointwise bound. -/
lemma sInf_image_mono {u v : EuclSpace d → ℝ} {s : Set (EuclSpace d)}
    (hs : s.Nonempty) (hu : BddBelow (u '' s)) (h : ∀ y, u y ≤ v y) :
    sInf (u '' s) ≤ sInf (v '' s) := by
  refine le_csInf (hs.image v) ?_
  rintro a ⟨y, hy, rfl⟩
  exact le_trans (csInf_le hu ⟨y, hy, rfl⟩) (h y)

/-! ### The operator -/

/-- **The tug-of-war step operator.** -/
def tugOfWarOp (p ε : ℝ) (v : EuclSpace d → ℝ) (x : EuclSpace d) : ℝ :=
  (p - 2) / (p + (d : ℝ)) / 2 *
      (sSup (v '' closedBall x ε) + sInf (v '' closedBall x ε))
    + ((d : ℝ) + 2) / (p + (d : ℝ)) * (⨍ y in ball x ε, v y)

/-- The weights are a partition of unity: `α + β = 1`. -/
lemma alpha_add_beta (p : ℝ) (hp : 0 < p + (d : ℝ)) :
    (p - 2) / (p + (d : ℝ)) + ((d : ℝ) + 2) / (p + (d : ℝ)) = 1 := by
  field_simp
  ring

/-- **Monotonicity of the step operator, for `2 ≤ p`.**

The hypothesis `2 ≤ p` is essential: for `1 < p < 2` the weight `α` is negative
and the `sup + inf` term is anti-monotone. -/
theorem tugOfWarOp_monotone (p ε : ℝ) (hp : 2 ≤ p) (hd : 0 < d) (hε : 0 < ε)
    {u v : EuclSpace d → ℝ} (hu : BddMeas u) (hv : BddMeas v)
    (h : ∀ y, u y ≤ v y) (x : EuclSpace d) :
    tugOfWarOp p ε u x ≤ tugOfWarOp p ε v x := by
  have hpd : 0 < p + (d : ℝ) := by positivity
  have hα : 0 ≤ (p - 2) / (p + (d : ℝ)) / 2 := by
    apply div_nonneg (div_nonneg (by linarith) hpd.le)
    norm_num
  have hβ : 0 ≤ ((d : ℝ) + 2) / (p + (d : ℝ)) := by positivity
  have hne := nonempty_closedBall x hε.le
  have hsup := sSup_image_mono (u := u) (v := v) hne (hv.bddAbove_image x ε) h
  have hinf := sInf_image_mono (u := u) (v := v) hne (hu.bddBelow_image x ε) h
  have havg := setAverage_mono_ball x (hu.integrableOn_ball x ε)
    (hv.integrableOn_ball x ε) h
  unfold tugOfWarOp
  gcongr


/-! ### Translation equivariance

Adding a constant to the input shifts the output by the same constant. Together
with monotonicity this yields nonexpansiveness without any further estimation of
extreme values.
-/

lemma bddAbove_image_add_const {t : Set ℝ} (K : ℝ) (hb : BddAbove t) :
    BddAbove ((fun r => r + K) '' t) := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨M + K, ?_⟩
  rintro a ⟨r, hr, rfl⟩
  have := hM hr
  simp only
  linarith

lemma bddBelow_image_add_const {t : Set ℝ} (K : ℝ) (hb : BddBelow t) :
    BddBelow ((fun r => r + K) '' t) := by
  obtain ⟨M, hM⟩ := hb
  refine ⟨M + K, ?_⟩
  rintro a ⟨r, hr, rfl⟩
  have := hM hr
  simp only
  linarith

lemma sSup_image_add_const (t : Set ℝ) (K : ℝ) (ht : t.Nonempty)
    (hb : BddAbove t) :
    sSup ((fun r => r + K) '' t) = sSup t + K := by
  have hbi := bddAbove_image_add_const K hb
  refine le_antisymm (csSup_le (ht.image _) ?_) ?_
  · rintro a ⟨r, hr, rfl⟩
    have := le_csSup hb hr
    simp only
    linarith
  · have h : sSup t ≤ sSup ((fun r => r + K) '' t) - K := by
      refine csSup_le ht fun r hr => ?_
      have := le_csSup hbi ⟨r, hr, rfl⟩
      simp only at this
      linarith
    linarith

lemma sInf_image_add_const (t : Set ℝ) (K : ℝ) (ht : t.Nonempty)
    (hb : BddBelow t) :
    sInf ((fun r => r + K) '' t) = sInf t + K := by
  have hbi := bddBelow_image_add_const K hb
  refine le_antisymm ?_ (le_csInf (ht.image _) ?_)
  · have h : sInf ((fun r => r + K) '' t) - K ≤ sInf t := by
      refine le_csInf ht fun r hr => ?_
      have := csInf_le hbi ⟨r, hr, rfl⟩
      simp only at this
      linarith
    linarith
  · rintro a ⟨r, hr, rfl⟩
    have := csInf_le hb hr
    simp only
    linarith

/-- **Translation equivariance of the step operator.** -/
theorem tugOfWarOp_add_const (p ε : ℝ) (hε : 0 < ε)
    {v : EuclSpace d → ℝ} (hv : BddMeas v) (K : ℝ) (x : EuclSpace d)
    (hpd : 0 < p + (d : ℝ)) :
    tugOfWarOp p ε (fun y => v y + K) x = tugOfWarOp p ε v x + K := by
  have hne : (v '' closedBall x ε).Nonempty :=
    ⟨v x, x, mem_closedBall_self hε.le, rfl⟩
  have hab := hv.bddAbove_image x ε
  have hbb := hv.bddBelow_image x ε
  have himg : (fun y => v y + K) '' closedBall x ε
      = (fun r => r + K) '' (v '' closedBall x ε) := by
    rw [Set.image_image]
  have havg : (⨍ y in ball x ε, (v y + K))
      = (⨍ y in ball x ε, v y) + K := by
    rw [show (fun y => v y + K) = v + (fun _ => K) from rfl,
        MeasureTheory.setAverage_add (hv.integrableOn_ball x ε)
          integrableOn_const,
        setAverage_const_ball K x hε]
  unfold tugOfWarOp
  rw [himg, sSup_image_add_const _ K hne hab,
      sInf_image_add_const _ K hne hbb, havg]
  have h1 := alpha_add_beta (d := d) p hpd
  field_simp
  ring_nf


/-! ### Nonexpansiveness

The operator is nonexpansive in the sup norm but *not* contractive. This is the
structural reason uniqueness for the discrete problem does not follow from a
fixed point theorem, and why the comparison argument needs a strict concave
perturbation.
-/

/-- Adding a constant preserves `BddMeas`. -/
lemma BddMeas.add_const' {v : EuclSpace d → ℝ} (hv : BddMeas v) (K : ℝ) :
    BddMeas (fun y => v y + K) := by
  obtain ⟨C, hC⟩ := hv.bound
  refine ⟨hv.meas.add_const K, ⟨C + |K|, fun y => ?_⟩⟩
  calc |v y + K| ≤ |v y| + |K| := abs_add_le _ _
    _ ≤ C + |K| := by linarith [hC y]

/-- A two-sided bound gives the pointwise inequality monotonicity needs. -/
lemma le_add_of_abs_sub_le {u v : EuclSpace d → ℝ} {K : ℝ}
    (h : ∀ y, |u y - v y| ≤ K) (y : EuclSpace d) : u y ≤ v y + K := by
  have := (abs_le.1 (h y)).2
  linarith

/-- **Nonexpansiveness in the sup norm.** -/
theorem tugOfWarOp_nonexpansive (p ε : ℝ) (hp : 2 ≤ p) (hd : 0 < d)
    (hε : 0 < ε) (hpd : 0 < p + (d : ℝ))
    {u v : EuclSpace d → ℝ} (hu : BddMeas u) (hv : BddMeas v) {K : ℝ}
    (h : ∀ y, |u y - v y| ≤ K) (x : EuclSpace d) :
    |tugOfWarOp p ε u x - tugOfWarOp p ε v x| ≤ K := by
  have h1 : tugOfWarOp p ε u x ≤ tugOfWarOp p ε v x + K := by
    have := tugOfWarOp_monotone p ε hp hd hε hu (hv.add_const' K)
      (le_add_of_abs_sub_le h) x
    rwa [tugOfWarOp_add_const p ε hε hv K x hpd] at this
  have h2 : tugOfWarOp p ε v x ≤ tugOfWarOp p ε u x + K := by
    have hsym : ∀ y, |v y - u y| ≤ K := fun y => by
      rw [abs_sub_comm]; exact h y
    have := tugOfWarOp_monotone p ε hp hd hε hv (hu.add_const' K)
      (le_add_of_abs_sub_le hsym) x
    rwa [tugOfWarOp_add_const p ε hε hu K x hpd] at this
  rw [abs_le]
  constructor <;> linarith

end PLaplacian
