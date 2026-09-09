/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Plaplacian.ExtremeValues
import Plaplacian.StepOperator

/-!
# The strictly concave perturbation

The step operator `T_ε` is nonexpansive but not contractive, so uniqueness for
the discrete problem does not follow from a fixed point theorem, and a
comparison argument at a maximum of `v - u` yields only a non-strict
inequality. The standard remedy is to perturb by a strictly concave function.

This file computes `T_ε ψ` in closed form for `ψ x = R ^ 2 - ‖x‖ ^ 2` and
derives the quantitative gap

  `ψ x - T_ε ψ x = α ε ^ 2 + β * m ε`

where `m ε` is the second moment of the centred ball of radius `ε`. Both terms
are nonnegative for `2 ≤ p` and the second is strictly positive, which is
exactly the strictness the comparison principle needs.

## How the computation goes

The extreme values swap: since `ψ` is a decreasing function of `‖·‖`, the
supremum of `ψ` over a ball comes from the *infimum* of the norm and vice
versa. `AntitoneOn.map_isLeast` and `AntitoneOn.map_isGreatest` transport the
results of `Plaplacian.ExtremeValues` across `t ↦ R ^ 2 - t ^ 2`. Summing,

  `sup ψ + inf ψ = 2 ψ x - 2 ε ^ 2`,

while the average contributes `ψ x - m ε` by `setAverage_normSq_ball`, whose
proof uses the odd moments of `Plaplacian.BallMoments`. Combining with
`α + β = 1` gives the gap.

## Main results

- `psi`: the perturbation `R ^ 2 - ‖x‖ ^ 2`.
- `isGreatest_psi`, `isLeast_psi`: its extreme values on a ball.
- `sSup_add_sInf_psi`: the extreme values sum to `2 ψ x - 2 ε ^ 2`.
- `setAverage_psi`: the average is `ψ x - m ε`.
- `psi_sub_tugOfWarOp`: **the gap.**

## Hypotheses

`x ≠ 0` and `ε ≤ ‖x‖` are needed because the infimum of the norm over
`ball x ε` degenerates to `0` when the ball contains the origin; see
`Plaplacian.ExtremeValues.isLeast_norm_closedBall_zero` for that case, which is
not yet combined into the gap.
-/

open MeasureTheory Metric Set

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-- The strictly concave perturbation. Note this is *not* globally bounded, so
it is not in `BddMeas`; the comparison argument uses it on a bounded domain. -/
def psi (R : ℝ) (x : EuclSpace d) : ℝ := R ^ 2 - ‖x‖ ^ 2

lemma continuous_psi (R : ℝ) : Continuous (psi (d := d) R) := by
  unfold psi; fun_prop

lemma measurable_psi (R : ℝ) : Measurable (psi (d := d) R) :=
  (continuous_psi R).measurable

/-! ### Extreme values of `ψ`, by antitone transport -/

lemma psi_image (R : ℝ) (x : EuclSpace d) (ε : ℝ) :
    psi R '' closedBall x ε
      = (fun t : ℝ => R ^ 2 - t ^ 2) ''
          ((fun y : EuclSpace d => ‖y‖) '' closedBall x ε) := by
  rw [Set.image_image]; rfl

lemma antitoneOn_sub_sq (R : ℝ) :
    AntitoneOn (fun t : ℝ => R ^ 2 - t ^ 2) (Ici (0:ℝ)) := by
  intro a ha b hb hab
  simp only [mem_Ici] at ha hb
  have : a ^ 2 ≤ b ^ 2 := by nlinarith
  linarith

lemma norm_image_subset_Ici (x : EuclSpace d) (ε : ℝ) :
    (fun y : EuclSpace d => ‖y‖) '' closedBall x ε ⊆ Ici (0:ℝ) := by
  rintro a ⟨y, -, rfl⟩; exact norm_nonneg y

/-- The supremum of `ψ` comes from the infimum of the norm. -/
theorem isGreatest_psi (R : ℝ) {x : EuclSpace d} (hx : x ≠ 0) {ε : ℝ}
    (hε : 0 ≤ ε) (hle : ε ≤ ‖x‖) :
    IsGreatest (psi R '' closedBall x ε) (R ^ 2 - (‖x‖ - ε) ^ 2) := by
  rw [psi_image]
  exact ((antitoneOn_sub_sq R).mono (norm_image_subset_Ici x ε)).map_isLeast
    (isLeast_norm_closedBall hx hε hle)

/-- The infimum of `ψ` comes from the supremum of the norm. -/
theorem isLeast_psi (R : ℝ) {x : EuclSpace d} (hx : x ≠ 0) {ε : ℝ}
    (hε : 0 ≤ ε) :
    IsLeast (psi R '' closedBall x ε) (R ^ 2 - (‖x‖ + ε) ^ 2) := by
  rw [psi_image]
  exact ((antitoneOn_sub_sq R).mono (norm_image_subset_Ici x ε)).map_isGreatest
    (isGreatest_norm_closedBall hx hε)

/-- The extreme values sum to `2 ψ x - 2 ε ^ 2`: the `ε ^ 2` deficit is the
first source of strictness. -/
theorem sSup_add_sInf_psi (R : ℝ) {x : EuclSpace d} (hx : x ≠ 0) {ε : ℝ}
    (hε : 0 ≤ ε) (hle : ε ≤ ‖x‖) :
    sSup (psi R '' closedBall x ε) + sInf (psi R '' closedBall x ε)
      = 2 * psi R x - 2 * ε ^ 2 := by
  rw [(isGreatest_psi R hx hε hle).csSup_eq, (isLeast_psi R hx hε).csInf_eq]
  unfold psi; ring

/-! ### The average of `ψ` -/

lemma integrableOn_normSq_ball (x : EuclSpace d) (ε : ℝ) :
    IntegrableOn (fun y : EuclSpace d => ‖y‖ ^ 2) (ball x ε) :=
  (ContinuousOn.integrableOn_compact (isCompact_closedBall _ _)
    (by fun_prop)).mono_set ball_subset_closedBall

lemma setAverage_const_sub (c : ℝ) (f : EuclSpace d → ℝ) (x : EuclSpace d)
    {ε : ℝ} (hε : 0 < ε) (hf : IntegrableOn f (ball x ε)) :
    (⨍ y in ball x ε, (c - f y)) = c - ⨍ y in ball x ε, f y := by
  have hc : IntegrableOn (fun _ : EuclSpace d => c) (ball x ε) :=
    integrableOn_const
  have h1 : (fun y : EuclSpace d => c - f y)
      = (fun _ : EuclSpace d => c) - f := by funext y; rfl
  rw [h1, MeasureTheory.setAverage_sub hc hf, setAverage_const_ball c x hε]

/-- The average of `ψ` falls short of `ψ x` by the second moment: the second
source of strictness. -/
theorem setAverage_psi (R : ℝ) (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    (⨍ y in ball x ε, psi R y)
      = psi R x - ⨍ z in ball (0 : EuclSpace d) ε, ‖z‖ ^ 2 := by
  unfold psi
  rw [setAverage_const_sub (R ^ 2) (fun y => ‖y‖ ^ 2) x hε
        (integrableOn_normSq_ball x ε),
      setAverage_normSq_ball x hε]
  ring

/-! ### The gap: withdrawn

An earlier version proved
`ψ x - T_ε ψ x = α ε ^ 2 + β * (second moment)`,
combining `sSup_add_sInf_psi` with the definition of `tugOfWarOp`. That is no
longer available, for two independent reasons.

* `tugOfWarOp` now takes its extreme values over OPEN balls (forced by
  measurability; see `Plaplacian.Measurability`). Over an open ball the extreme
  values of `ψ` are approached but not attained, so `isGreatest_psi` and
  `isLeast_psi` below --- which are about `closedBall` --- do not convert to
  `sSup`/`sInf` of the open-ball image via `IsGreatest.csSup_eq`.

* More fundamentally, the gap does not lead anywhere. `T_ε` is neither sub-
  nor superadditive: the supremum is subadditive and the infimum is
  superadditive, so the pair `sup + inf` is neither. Hence one cannot split
  `T_ε (u + δψ) ≤ T_ε u + δ T_ε ψ`, which is the step a
  "perturb and split" comparison proof requires.

The comparison principle is instead obtained by the game-free argument of
Luiro--Parviainen--Saksman, which uses no perturbation at all. The material
retained above (extreme values of `ψ` on a closed ball, and the average of
`ψ` over a ball) is correct and self-contained, and is kept for the record.
-/

end PLaplacian
