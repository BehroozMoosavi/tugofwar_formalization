/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Order2

@[expose] public section

/-!
# Order-two Taylor in plain deriv form

For a C-three function of one variable there is a point of the open unit
interval at which

  g 1 = g 0 + g prime 0 + one half g double prime 0 + one sixth g triple
  prime at that point.

This is taylor_mean_remainder_lagrange at order two, with every
iteratedDerivWithin term translated into plain deriv.

## Why order two, and why one dimension

The remainder for the average expansion must be of order three in the
increment. Two earlier routes tried to obtain it multivariately and failed for
the same reason: Mathlib registers the space of continuous linear maps with
ContinuousLinearMap.topologicalSpace rather than the metric topology induced
by the operator norm, and Lean does not unify the two. So Continuous.norm is
unavailable on the Hessian, and HasFDerivAt.comp_hasDerivAt cannot compose
derivatives through the space of bilinear maps. The second derivative along a
line succeeds only because its intermediate space is one level lower, where
the instances happen to align; at the third derivative they do not.

This route never leaves the reals, and so never meets the obstruction.

## The two sides of the interval

The polynomial terms are evaluated at the base point, an endpoint of the unit
interval, while the remainder sits at an interior point. At an interior point
the interval is a neighbourhood and derivWithin_of_mem_nhds applies; at an
endpoint it is not, but a closed interval has unique differentiability there.
At order two the endpoint case needs more care still: the inner iterated
derivative must be shown to agree with the plain derivative on the whole
interval, not merely at the point, before a further derivative within can be
taken.

## Main results

- iteratedDerivWithin_two_endpoint
- taylor_two_deriv
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## Order-two Taylor in plain `deriv` form -/

theorem contDiffOn_two_of_three (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) :
    ContDiffOn ℝ 2 g (uIcc (0:ℝ) 1) :=
  (hg.of_le (by norm_num)).contDiffOn

theorem differentiableOn_iteratedDerivWithin_two (g : ℝ → ℝ)
    (hg : ContDiff ℝ 3 g) :
    DifferentiableOn ℝ (iteratedDerivWithin 2 g (uIcc (0:ℝ) 1))
      (uIoo (0:ℝ) 1) := by
  rw [uIoo_zero_one]
  intro t ht
  have htmm : t ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1) := by simpa using ht
  have heq : iteratedDerivWithin 2 g (uIcc (0:ℝ) 1) =ᶠ[nhds t]
      deriv (deriv g) :=
    iteratedDerivWithin_two_eventuallyEq g htmm
  have h1 : ContDiff ℝ 2 (deriv g) := ContDiff.deriv' hg
  have hd : DifferentiableAt ℝ (deriv (deriv g)) t :=
    (ContDiff.differentiable_deriv_two h1) t
  exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt

theorem iteratedDerivWithin_one_eqOn (g : ℝ → ℝ) (hg : Differentiable ℝ g)
    {a b : ℝ} (hab : a < b) :
    EqOn (iteratedDerivWithin 1 g (Icc a b)) (deriv g) (Icc a b) := by
  intro t ht
  exact iteratedDerivWithin_one_endpoint g hg hab ht

theorem iteratedDerivWithin_two_endpoint (g : ℝ → ℝ)
    (hg : ContDiff ℝ 2 g) {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) :
    iteratedDerivWithin 2 g (Icc a b) t = deriv (deriv g) t := by
  rw [show (2 : Nat) = 1 + 1 from rfl, iteratedDerivWithin_succ]
  have hcongr : derivWithin (iteratedDerivWithin 1 g (Icc a b)) (Icc a b) t
      = derivWithin (deriv g) (Icc a b) t := by
    apply derivWithin_congr
    · exact iteratedDerivWithin_one_eqOn g (hg.differentiable (by norm_num)) hab
    · exact iteratedDerivWithin_one_endpoint g
        (hg.differentiable (by norm_num)) hab ht
  rw [hcongr]
  exact (ContDiff.differentiable_deriv_two hg t).derivWithin
    (uniqueDiffOn_Icc hab t ht)

/-! ### The theorem -/

/-- **Order-two Taylor with Lagrange remainder, in plain `deriv` form.** -/
theorem taylor_two_deriv (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) :
    ∃ ξ ∈ Ioo (0:ℝ) 1,
      g 1 = g 0 + deriv g 0 + (1/2) * deriv (deriv g) 0
        + (1/6) * deriv (deriv (deriv g)) ξ := by
  obtain ⟨ξ, hξ, hres⟩ := taylor_mean_remainder_lagrange
    (f := g) (x₀ := 0) (x := 1) (n := 2)
    (by norm_num) (contDiffOn_two_of_three g hg)
    (differentiableOn_iteratedDerivWithin_two g hg)
  rw [uIoo_zero_one] at hξ
  refine ⟨ξ, hξ, ?_⟩
  have htmm : ξ ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1) := by simpa using hξ
  rw [uIcc_zero_one] at hres
  rw [taylorWithinEval_two] at hres
  rw [iteratedDerivWithin_one_endpoint g (hg.differentiable (by norm_num))
        (by norm_num) (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1)] at hres
  rw [iteratedDerivWithin_two_endpoint g (hg.of_le (by norm_num))
        (by norm_num) (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1)] at hres
  rw [← uIcc_zero_one, iteratedDerivWithin_three_eq g htmm] at hres
  norm_num at hres
  linarith [hres]

end

end PLaplacian
