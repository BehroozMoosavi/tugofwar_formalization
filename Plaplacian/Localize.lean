/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.GradDir

@[expose] public section

/-!
# Localization of the maximizer

The extreme-value expansion requires that the maximizer of a test function
over a ball lie close to the point obtained by stepping epsilon in the
gradient direction. Our own analysis had identified this as the hardest single
step in the project.

It reduces to a polarization identity. If the maximizer is y, then phi at y is
at least phi at the shifted point, and expanding both about the centre makes
the linear functional nearly maximal on the ball. Since that functional attains
its maximum over the ball only at the shifted point, a deficit c in the inner
product bounds the squared distance by two epsilon c:

  the squared distance from y minus x to epsilon nu equals the squared norm of
  y minus x, minus twice epsilon times the inner product, plus epsilon
  squared, and the first term is at most epsilon squared.

With c of order epsilon squared from the Taylor comparison, the maximizer is
within order epsilon to the three halves of the shifted point.

## Main results

- norm_sub_shift_sq: the polarization identity.
- norm_sub_shift_le: the localization bound.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## Localization of the maximizer

If `y` maximizes `φ` on the closed ball then `φ y ≥ φ (x + ε ν)`, and
expanding both sides about `x` makes the linear functional nearly maximal on
the ball. Since the maximum of `⟪∇φ x, ·⟫` over the ball is attained only at
`ε ν`, that forces `y` near `x + ε ν`.

The quantitative mechanism is the polarization identity below: a deficit `c`
in the inner product gives distance at most the square root of `2 ε c`. With
`c` of order `ε²` from the Taylor comparison, the maximizer is within
`O(ε^{3/2})` of the shifted point.
-/

/-- **Polarization.** The squared distance to the shifted point. -/
theorem norm_sub_shift_sq (x y : EuclSpace d) {ν : EuclSpace d}
    (hν : ‖ν‖ = 1) (ε : ℝ) :
    ‖y - x - ε • ν‖ ^ 2
      = ‖y - x‖ ^ 2 - 2 * ε * inner ℝ ν (y - x) + ε ^ 2 := by
  rw [norm_sub_sq_real (y - x) (ε • ν), norm_smul, hν, Real.norm_eq_abs,
      mul_one]
  have hinner : inner ℝ (y - x) (ε • ν) = ε * inner ℝ ν (y - x) := by
    rw [real_inner_smul_right, real_inner_comm]
  rw [hinner, sq_abs]
  ring

/-- **The localization bound.** A deficit `c` in the inner product bounds the
squared distance by `2 ε c`. -/
theorem norm_sub_shift_le (x y : EuclSpace d) {ν : EuclSpace d}
    (hν : ‖ν‖ = 1) {ε c : ℝ} (hε : 0 < ε)
    (hball : ‖y - x‖ ≤ ε) (hinner : ε - c ≤ inner ℝ ν (y - x)) :
    ‖y - x - ε • ν‖ ^ 2 ≤ 2 * ε * c := by
  rw [norm_sub_shift_sq x y hν ε]
  have hsq : ‖y - x‖ ^ 2 ≤ ε ^ 2 := by
    have h0 : (0:ℝ) ≤ ‖y - x‖ := norm_nonneg _
    nlinarith [hball, h0]
  nlinarith [hsq, hinner, hε]

end

end PLaplacian
