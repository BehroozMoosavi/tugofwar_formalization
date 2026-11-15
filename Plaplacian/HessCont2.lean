/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.SingEigen

@[expose] public section

/-!
# The Hessian quadratic form, continuous uniformly

Near the maximum, the Hessian quadratic form at a nearby point exceeds the one
at the maximum by at most a prescribed multiple of the squared norm, uniformly
in the direction. That is continuity of the Hessian in the operator norm,
which the curried representation does not support and the flat second
derivative does.

## Main results

- hess_quad_cont
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The Hessian quadratic form, continuous uniformly

The singular argument compares the Hessian at the near-maximizer with the
Hessian at the maximum, uniformly over the direction:

  `D²φ(y)(z,z) ≤ D²φ(x₀)(z,z) + η ‖z‖²` near `x₀`.

That is continuity of the Hessian in the operator norm, which the curried
representation does not support. The flat second derivative does. The
difference of the two quadratic forms is the flat multilinear map
`iteratedFDeriv 2 φ y - iteratedFDeriv 2 φ x₀` applied to `(z, z)`, bounded by
its operator norm times `‖z‖²`; and that operator norm tends to zero because
the flat second derivative is continuous for a `C³` function.

This is the fifth time the flat representation has been the way past the
curried one's topology.
-/


/-- **The Hessian quadratic form is continuous, uniformly in the direction.** -/
theorem hess_quad_cont {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x₀ : EuclSpace d) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ y ∈ ball x₀ ρ, ∀ z : EuclSpace d,
      (fderiv ℝ (fderiv ℝ φ) y z) z
        ≤ (fderiv ℝ (fderiv ℝ φ) x₀ z) z + η * ‖z‖ ^ 2 := by
  have hc : Continuous (fun x => iteratedFDeriv ℝ 2 φ x) :=
    hφ.continuous_iteratedFDeriv (by norm_num)
  obtain ⟨ρ, hρ, hball⟩ := Metric.continuousAt_iff.1 hc.continuousAt η hη
  refine ⟨ρ, hρ, fun y hy z => ?_⟩
  have hd : ‖iteratedFDeriv ℝ 2 φ y - iteratedFDeriv ℝ 2 φ x₀‖ < η := by
    rw [← dist_eq_norm]; exact hball (mem_ball.1 hy)
  -- the curried quadratic form as the flat map on (z, z)
  have hA : ∀ w : EuclSpace d, iteratedFDeriv ℝ 2 φ w ![z, z]
      = (fderiv ℝ (fderiv ℝ φ) w z) z := by
    intro w; rw [iteratedFDeriv_two_apply]; simp
  have hdiff : (fderiv ℝ (fderiv ℝ φ) y z) z - (fderiv ℝ (fderiv ℝ φ) x₀ z) z
      = (iteratedFDeriv ℝ 2 φ y - iteratedFDeriv ℝ 2 φ x₀) ![z, z] := by
    rw [sub_apply, hA, hA]
  -- the product of the norms of (z, z)
  have hprod : ∏ i : Fin 2, ‖(![z, z] : Fin 2 → EuclSpace d) i‖ = ‖z‖ ^ 2 := by
    simp [Fin.prod_univ_two, sq]
  -- the flat map's value is bounded by its norm
  have h1 : (iteratedFDeriv ℝ 2 φ y - iteratedFDeriv ℝ 2 φ x₀) ![z, z]
      ≤ ‖iteratedFDeriv ℝ 2 φ y - iteratedFDeriv ℝ 2 φ x₀‖ * ‖z‖ ^ 2 := by
    have := (iteratedFDeriv ℝ 2 φ y - iteratedFDeriv ℝ 2 φ x₀).le_opNorm ![z, z]
    rw [hprod, Real.norm_eq_abs] at this
    exact le_trans (le_abs_self _) this
  have h2 : ‖iteratedFDeriv ℝ 2 φ y - iteratedFDeriv ℝ 2 φ x₀‖ * ‖z‖ ^ 2
      ≤ η * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right hd.le (sq_nonneg _)
  linarith [hdiff, h1, h2]

end

end PLaplacian
