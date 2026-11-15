/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.TaylorInfra

@[expose] public section

/-!
# One-dimensional Taylor at order one, in plain deriv form

For a twice continuously differentiable `g` there is `ξ` in the open unit
interval with

  `g 1 = g 0 + deriv g 0 + (1/2) * deriv (deriv g) ξ`.

This is `taylor_mean_remainder_lagrange` at `n = 1`, with the
`iteratedDerivWithin` terms translated into plain `deriv` by
`Plaplacian.TaylorInfra`. The translated form is what the several-variable
expansion needs, since the line machinery of `Plaplacian.LineRestrict`
produces `deriv` and not `iteratedDerivWithin`.

## Discharging the hypotheses

The theorem has two, and the second is the interesting one. It asks that
`iteratedDerivWithin 1 g (uIcc 0 1)` be differentiable on the *open* interval.
On the interior that function agrees with `deriv g` on a whole neighbourhood,
by `derivWithin_eventuallyEq`, and `deriv g` is differentiable because `g` is
`C²`; `DifferentiableAt.congr_of_eventuallyEq` then transfers
differentiability across the agreement. This is where the neighbourhood form of
the translation earns its place: the pointwise identity would not suffice,
since differentiability is not a pointwise property.

## Main results

- `taylor_one_deriv`
-/

open Set Topology Filter

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## One-dimensional Taylor at order one, in plain `deriv` form

The target:

  for a `C²` function `g` there is `ξ ∈ Ioo 0 1` with
  `g 1 = g 0 + deriv g 0 + (1/2) * deriv (deriv g) ξ`.

This is `taylor_mean_remainder_lagrange` at `n = 1` with the
`iteratedDerivWithin` terms translated by `Plaplacian.TaylorInfra`.
-/


/-- `uIoo 0 1` is `Ioo 0 1`. -/
theorem uIoo_zero_one : uIoo (0 : ℝ) 1 = Ioo 0 1 := by
  rw [uIoo_of_le (by norm_num : (0:ℝ) ≤ 1)]

/-- Taylor's first hypothesis. -/
theorem contDiffOn_of_contDiff (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) :
    ContDiffOn ℝ 1 g (uIcc (0:ℝ) 1) := by
  refine ContDiff.contDiffOn ?_
  exact hg.of_le (by norm_num)

/-- Taylor's second hypothesis: the within-derivative is differentiable on the
open interval, because there it agrees with `deriv g` on a neighbourhood. -/
theorem differentiableOn_iteratedDerivWithin_one (g : ℝ → ℝ)
    (hg : ContDiff ℝ 2 g) :
    DifferentiableOn ℝ (iteratedDerivWithin 1 g (uIcc (0:ℝ) 1))
      (uIoo (0:ℝ) 1) := by
  rw [uIoo_zero_one]
  intro t ht
  have htmm : t ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1) := by
    simpa using ht
  have heq : iteratedDerivWithin 1 g (uIcc (0:ℝ) 1) =ᶠ[nhds t] deriv g := by
    rw [iteratedDerivWithin_one]
    exact derivWithin_eventuallyEq g htmm
  have hd : DifferentiableAt ℝ (deriv g) t :=
    (ContDiff.differentiable_deriv_two hg) t
  exact ((hd.congr_of_eventuallyEq heq).differentiableWithinAt)

/-- **One-dimensional Taylor at order one, in plain `deriv` form.** -/
theorem taylor_one_deriv (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g) :
    ∃ ξ ∈ Ioo (0:ℝ) 1,
      g 1 = g 0 + deriv g 0 + (1/2) * deriv (deriv g) ξ := by
  obtain ⟨ξ, hξ, hres⟩ := taylor_mean_remainder_lagrange
    (f := g) (x₀ := 0) (x := 1) (n := 1)
    (by norm_num) (contDiffOn_of_contDiff g hg)
    (differentiableOn_iteratedDerivWithin_one g hg)
  rw [uIoo_zero_one] at hξ
  refine ⟨ξ, hξ, ?_⟩
  have htmm : ξ ∈ Ioo (min (0:ℝ) 1) (max (0:ℝ) 1) := by simpa using hξ
  rw [uIcc_zero_one] at hres
  rw [taylorWithinEval_one_unit_deriv g (hg.differentiable (by norm_num))]
    at hres
  rw [← uIcc_zero_one, iteratedDerivWithin_two_eq g htmm] at hres
  norm_num at hres
  linarith [hres]

end

end PLaplacian
