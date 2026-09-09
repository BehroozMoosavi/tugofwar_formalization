/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Plaplacian.Measurability

/-!
# The key estimate for the comparison principle

This file proves the analytic content of the comparison principle of
Luiro--Parviainen--Saksman (*On the existence and uniqueness of `p`-harmonious
functions*, Differential Integral Equations 27 (2014), Thm. 2.2): for two
solutions of the dynamic programming principle,

  `v x - u x ≤ α * sup_{B ε x} (v - u) + β * ⨍_{B ε x} (v - u)`.

Weighting the two difference estimates of `Plaplacian.Measurability` by `α/2`
each produces the factor `α` on the supremum term.

## Why not a perturbation argument

The informal remedy for the non-strictness of nonexpansiveness is to perturb by
a strictly concave function. That route is unavailable: `T_ε` is neither sub-
nor superadditive, since the supremum is subadditive while the infimum is
superadditive, so the pair `sup + inf` is neither. Hence
`T_ε (u + δψ) ≤ T_ε u + δ T_ε ψ` fails in both directions and the perturbation
cannot be split off. See the withdrawn section of `Plaplacian.Perturbation`.
LPS avoid perturbing altogether.

## Main results

- `BddMeas.sub`: the admissible class is closed under differences.
- `key_estimate`: the estimate above.

## TODO

The remainder of LPS Thm. 2.2 is topological rather than estimative: set
`M = sup_Ω (v - u)` and `G = {x | (v - u) x = M}`, deduce from `key_estimate`
that `G` is non-empty and that `|B ε x \ G| = 0` for every `x ∈ G`, and observe
that this propagation contradicts boundedness of `Ω`.
-/

open MeasureTheory Metric Set

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-- The difference of two admissible functions is admissible. -/
lemma BddMeas.sub {u v : EuclSpace d → ℝ} (hu : BddMeas u) (hv : BddMeas v) :
    BddMeas (fun y => u y - v y) := by
  obtain ⟨Cu, hCu⟩ := hu.bound
  obtain ⟨Cv, hCv⟩ := hv.bound
  refine ⟨hu.meas.sub hv.meas, ⟨Cu + Cv, fun y => ?_⟩⟩
  calc |u y - v y| ≤ |u y| + |v y| := abs_sub _ _
    _ ≤ Cu + Cv := by linarith [hCu y, hCv y]

/-- **The key estimate.** -/
theorem key_estimate (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ))
    {u v : EuclSpace d → ℝ} (hu : BddMeas u) (hv : BddMeas v)
    (x : EuclSpace d) :
    tugOfWarOp p ε v x - tugOfWarOp p ε u x
      ≤ (p - 2) / (p + (d : ℝ)) * sSup ((fun y => v y - u y) '' ball x ε)
        + ((d : ℝ) + 2) / (p + (d : ℝ))
            * ⨍ y in ball x ε, (v y - u y) := by
  have hne := nonempty_ball x hε
  have hdiff := hv.sub hu
  have hsup := sSup_sub_sSup_le u v (ball x ε) hne
    (hu.bddAbove_image (ball x ε)) (hdiff.bddAbove_image (ball x ε))
  have hinf := sInf_sub_sInf_le u v (ball x ε) hne
    (hv.bddBelow_image (ball x ε)) (hdiff.bddAbove_image (ball x ε))
  have havg : (⨍ y in ball x ε, v y) - (⨍ y in ball x ε, u y)
      = ⨍ y in ball x ε, (v y - u y) := by
    rw [show (fun y : EuclSpace d => v y - u y) = v - u from rfl,
        MeasureTheory.setAverage_sub (hv.integrableOn_ball x ε)
          (hu.integrableOn_ball x ε)]
  have hα : 0 ≤ (p - 2) / (p + (d : ℝ)) / 2 := by
    apply div_nonneg (div_nonneg (by linarith) hpd.le); norm_num
  unfold tugOfWarOp
  rw [← havg]
  nlinarith [hsup, hinf, hα]



/-! ### The a.e.-equality step

LPS deduce from `key_estimate` that if `v - u` attains its maximum `M` at `x`,
then `v - u = M` almost everywhere on `B ε x`. The mechanism is that a function
bounded above by `M` whose average equals `M` must equal `M` a.e., which
reduces via `M - f` to the standard fact that a nonnegative integrable function
with vanishing integral is zero a.e.
-/

/-- A nonnegative integrable function with vanishing integral is zero a.e. -/
lemma ae_eq_zero_of_setIntegral_eq_zero
    {g : EuclSpace d → ℝ} {s : Set (EuclSpace d)}
    (hint : MeasureTheory.IntegrableOn g s) (hnn : ∀ y, 0 ≤ g y)
    (hzero : (∫ y in s, g y) = 0) :
    g =ᵐ[volume.restrict s] 0 := by
  refine (MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae ?_ hint).1 hzero
  exact Filter.Eventually.of_forall hnn

/-- **The a.e.-equality step.** A function bounded above by `M` whose average
over a ball equals `M` is equal to `M` almost everywhere on that ball. -/
theorem ae_eq_of_setAverage_eq_max
    {f : EuclSpace d → ℝ} {M : ℝ} (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε)
    (hint : MeasureTheory.IntegrableOn f (ball x ε))
    (hle : ∀ y, f y ≤ M)
    (havg : (⨍ y in ball x ε, f y) = M) :
    (fun y => M - f y) =ᵐ[volume.restrict (ball x ε)] 0 := by
  have hcint : MeasureTheory.IntegrableOn (fun _ : EuclSpace d => M)
      (ball x ε) := integrableOn_const
  have hgint : MeasureTheory.IntegrableOn (fun y => M - f y) (ball x ε) :=
    hcint.sub hint
  refine ae_eq_zero_of_setIntegral_eq_zero hgint
    (fun y => by linarith [hle y]) ?_
  have hsub : (⨍ y in ball x ε, (M - f y)) = 0 := by
    rw [show (fun y : EuclSpace d => M - f y)
          = (fun _ : EuclSpace d => M) - f from rfl,
        MeasureTheory.setAverage_sub hcint hint,
        setAverage_const_ball M x hε, havg, sub_self]
  rw [MeasureTheory.setAverage_eq] at hsub
  have hvol : volume.real (ball x ε) ≠ 0 := by
    have h1 : volume (ball x ε) ≠ 0 := measure_ball_ne_zero x hε
    have h2 : volume (ball x ε) ≠ ⊤ := measure_ball_lt_top.ne
    simp only [MeasureTheory.Measure.real]
    exact ne_of_gt (ENNReal.toReal_pos h1 h2)
  rw [smul_eq_mul, mul_eq_zero] at hsub
  rcases hsub with h | h
  · exact absurd (inv_eq_zero.1 h) hvol
  · exact h

end PLaplacian
