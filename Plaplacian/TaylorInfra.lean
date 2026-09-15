/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.LineRestrict

/-!
# Taylor infrastructure for the asymptotic expansion

The asymptotic expansion of the step operator needs the second-order Taylor
expansion of a test function. Mathlib does not provide it in several
variables: `HasFTaylorSeriesUpTo` has exactly three fields, `zero_eq`,
`fderiv` and `cont`, none of which is a remainder estimate, so the structure
asserts that a tower of multilinear maps consists of the successive
derivatives and is continuous but says nothing about approximation. Neither
`HasFTaylorSeriesUpToOn.approx` nor a second-order Peano form exists. Only the
one-dimensional `taylor_mean_remainder_lagrange` supplies a remainder.

This file therefore reduces the several-variable expansion to the
one-dimensional theorem, along the lines through the base point, reusing the
machinery of `Plaplacian.LineRestrict`. Setting `g t = φ (x + t z)`, that file
already gives `g' t = Dφ (x + t z) z`; here we add the second derivative at an
arbitrary point of the line, continuity of the Hessian, and the translation
between `iteratedDerivWithin` --- in which the one-dimensional theorem is
stated --- and plain `deriv`.

## The two sides of the interval

The translation needs care at the two kinds of point. At an interior point the
interval is a *neighbourhood*, so `derivWithin_of_mem_nhds` applies and, at
order two, `Filter.EventuallyEq.deriv_eq` handles the inner derivative. At an
endpoint --- and the base point of the Taylor expansion is the endpoint `0` of
`[0,1]` --- the interval is not a neighbourhood, but a closed interval has
unique differentiability there, so `DifferentiableAt.derivWithin` applies
instead. Both cases are needed: the first derivative is evaluated at the
endpoint and the second at an interior point.

## Main results

- `hasDerivAt_second_at`: the second derivative along a line, at any point.
- `continuous_hess`: continuity of the Hessian.
- `uIcc_mem_nhds`, `iteratedDerivWithin_one_eq`,
  `iteratedDerivWithin_two_eq`: the interior translation.
- `iteratedDerivWithin_one_endpoint`: the endpoint translation.
- `taylorWithinEval_one`, `taylorWithinEval_one_unit_deriv`: the Taylor
  polynomial in closed form.
-/

open Set Topology Filter

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-! ### The line, at an arbitrary point -/

/-- The second derivative along a line, at any point of it. The base-point
case is `hasDerivAt_second`; the general case holds because
`hasFDerivAt_fderiv` and `hasDerivAt_lineMap` hold everywhere. -/
theorem hasDerivAt_second_at {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x z : EuclSpace d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => fderiv ℝ φ (lineMap x z s) z)
      (fderiv ℝ (fderiv ℝ φ) (lineMap x z t) z z) t := by
  have hcomp : HasDerivAt (fun s : ℝ => fderiv ℝ φ (lineMap x z s))
      (fderiv ℝ (fderiv ℝ φ) (lineMap x z t) z) t := by
    have h1 : HasFDerivAt (fderiv ℝ φ)
        (fderiv ℝ (fderiv ℝ φ) (lineMap x z t)) (lineMap x z t) :=
      hasFDerivAt_fderiv hφ _
    exact h1.comp_hasDerivAt t (hasDerivAt_lineMap x z t)
  have heval : HasFDerivAt (fun L : EuclSpace d →L[ℝ] ℝ => L z)
      (ContinuousLinearMap.apply ℝ ℝ z)
      (fderiv ℝ φ (lineMap x z t)) :=
    (ContinuousLinearMap.apply ℝ ℝ z).hasFDerivAt
  have hres := heval.comp_hasDerivAt t hcomp
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply] at hres
  exact hres

/-- Continuity of the Hessian, needed to convert the Lagrange remainder into
a little-o estimate. -/
theorem continuous_hess {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ) :
    Continuous (fun y => fderiv ℝ (fderiv ℝ φ) y) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  exact h1.continuous_fderiv (by norm_num)

/-! ### Interior points: the neighbourhood route -/

theorem uIcc_mem_nhds {a b t : ℝ} (ht : t ∈ Ioo (min a b) (max a b)) :
    uIcc a b ∈ nhds t := by
  rw [uIcc]
  exact Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self

theorem iteratedDerivWithin_one_eq (g : ℝ → ℝ) {a b t : ℝ}
    (ht : t ∈ Ioo (min a b) (max a b)) :
    iteratedDerivWithin 1 g (uIcc a b) t = deriv g t := by
  rw [iteratedDerivWithin_one]
  exact derivWithin_of_mem_nhds (uIcc_mem_nhds ht)

/-- The inner derivative agrees with `deriv g` on a whole neighbourhood, which
is what licenses differentiating it again. -/
theorem derivWithin_eventuallyEq (g : ℝ → ℝ) {a b t : ℝ}
    (ht : t ∈ Ioo (min a b) (max a b)) :
    derivWithin g (uIcc a b) =ᶠ[nhds t] deriv g := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact derivWithin_of_mem_nhds (uIcc_mem_nhds hs)

/-- **The order-two translation.** -/
theorem iteratedDerivWithin_two_eq (g : ℝ → ℝ) {a b t : ℝ}
    (ht : t ∈ Ioo (min a b) (max a b)) :
    iteratedDerivWithin 2 g (uIcc a b) t = deriv (deriv g) t := by
  rw [show (2 : Nat) = 1 + 1 from rfl, iteratedDerivWithin_succ,
      iteratedDerivWithin_one]
  rw [derivWithin_of_mem_nhds (uIcc_mem_nhds ht)]
  exact (derivWithin_eventuallyEq g ht).deriv_eq

/-! ### Endpoints: the unique-differentiability route -/

/-- At an endpoint the interval is not a neighbourhood, but it has unique
differentiability, which suffices at order one. -/
theorem iteratedDerivWithin_one_endpoint (g : ℝ → ℝ)
    (hg : Differentiable ℝ g) {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) :
    iteratedDerivWithin 1 g (Icc a b) t = deriv g t := by
  rw [iteratedDerivWithin_one]
  exact (hg t).derivWithin (uniqueDiffOn_Icc hab t ht)

theorem uIcc_zero_one : uIcc (0 : ℝ) 1 = Icc 0 1 := by
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]

/-! ### The Taylor polynomial -/

theorem taylorWithinEval_one (g : ℝ → ℝ) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval g 1 s x₀ x
      = g x₀ + (x - x₀) * iteratedDerivWithin 1 g s x₀ := by
  rw [show (1 : Nat) = 0 + 1 from rfl, taylorWithinEval_succ,
      taylor_within_zero_eval]
  simp

theorem taylorWithinEval_one_unit (g : ℝ → ℝ) :
    taylorWithinEval g 1 (Icc (0:ℝ) 1) 0 1
      = g 0 + iteratedDerivWithin 1 g (Icc (0:ℝ) 1) 0 := by
  rw [taylorWithinEval_one]
  ring

/-- **The Taylor polynomial at order one on the unit interval**, with the
derivative identified. This is exactly what
`taylor_mean_remainder_lagrange` subtracts. -/
theorem taylorWithinEval_one_unit_deriv (g : ℝ → ℝ)
    (hg : Differentiable ℝ g) :
    taylorWithinEval g 1 (Icc (0:ℝ) 1) 0 1 = g 0 + deriv g 0 := by
  rw [taylorWithinEval_one_unit,
      iteratedDerivWithin_one_endpoint g hg (by norm_num)
        (by norm_num : (0:ℝ) ∈ Icc (0:ℝ) 1)]

end PLaplacian

end
