/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.CubicBound

/-!
# The line map derivative norms

For the composition bound that yields the cubic rate, the iterated
derivatives of the line map are needed: order one has norm equal to the norm
of the direction, and every higher order vanishes, the map being affine.

The first derivative is the span-singleton map determined by the direction,
whose norm is the direction's. For the second, the first derivative is a
constant function of the base point, so its derivative is zero, and the curry
isometry carries zero to zero.

These are the inputs to norm_iteratedFDeriv_comp_le with the bound on the
direction taken as its norm, which makes the resulting bound cubic in the
direction --- exactly what a rate for the error term requires.

## Main results

- fderiv_line, norm_fderiv_line
- iteratedFDeriv_two_line, norm_iteratedFDeriv_two_line
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The line map's derivative norms

For the composition bound, the line map's iterated derivatives are needed:
order one has norm `‖z‖`, and all higher orders vanish. The derivative of
`s ↦ x + s • z` is `smulRight (id) z`, whose norm is `‖z‖ * ‖id‖`; on the
reals the identity functional has norm one.
-/


/-- The line map is smooth to every order. -/
theorem contDiff_line (x z : EuclSpace d) (n : ℕ) :
    ContDiff ℝ n (fun s : ℝ => x + s • z) := by
  fun_prop

/-- Its Fréchet derivative, as a continuous linear map. -/
theorem fderiv_line (x z : EuclSpace d) (t : ℝ) :
    fderiv ℝ (fun s : ℝ => x + s • z) t
      = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) z := by
  have h : HasDerivAt (fun s : ℝ => x + s • z) z t := by
    simpa using (hasDerivAt_id t).smul_const z |>.const_add x
  exact h.hasFDerivAt.fderiv

/-- Hence the first derivative has norm `‖z‖`. -/
theorem norm_fderiv_line (x z : EuclSpace d) (t : ℝ) :
    ‖iteratedFDeriv ℝ 1 (fun s : ℝ => x + s • z) t‖ = ‖z‖ := by
  rw [norm_iteratedFDeriv_one, fderiv_line x z t,
      ContinuousLinearMap.norm_smulRight_apply]
  simp

/-! ## The line map's higher derivatives vanish

`iteratedFDeriv_succ_eq_comp_left` gives `D^{n+1} f` as a curry of
`D (D^n f)`. Since the line map's first derivative is the *constant* map
`t ↦ toSpanSingleton ℝ z`, its derivative vanishes, and the curry of zero is
zero.
-/


/-- The line map's first iterated derivative is constant in the base point. -/
theorem iteratedFDeriv_one_line_const (x z : EuclSpace d) :
    iteratedFDeriv ℝ 1 (fun s : ℝ => x + s • z)
      = fun _ => iteratedFDeriv ℝ 1 (fun s : ℝ => x + s • z) 0 := by
  funext t
  ext m
  rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply,
      fderiv_line x z t, fderiv_line x z 0]

/-- Hence the second iterated derivative vanishes. -/
theorem iteratedFDeriv_two_line (x z : EuclSpace d) (t : ℝ) :
    iteratedFDeriv ℝ 2 (fun s : ℝ => x + s • z) t = 0 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedFDeriv_succ_eq_comp_left]
  simp only [Function.comp_apply]
  rw [iteratedFDeriv_one_line_const x z]
  rw [show (fun _ : ℝ => iteratedFDeriv ℝ 1 (fun s : ℝ => x + s • z) 0)
      = Function.const ℝ (iteratedFDeriv ℝ 1 (fun s : ℝ => x + s • z) 0)
      from rfl, fderiv_const]
  exact LinearIsometryEquiv.map_zero _

/-- And so does its norm, which is what the composition bound needs. -/
theorem norm_iteratedFDeriv_two_line (x z : EuclSpace d) (t : ℝ) :
    ‖iteratedFDeriv ℝ 2 (fun s : ℝ => x + s • z) t‖ = 0 := by
  rw [iteratedFDeriv_two_line, norm_zero]


end

end PLaplacian
