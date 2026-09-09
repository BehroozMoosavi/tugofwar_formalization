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

end PLaplacian
