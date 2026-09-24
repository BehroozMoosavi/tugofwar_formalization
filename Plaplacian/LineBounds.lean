/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.LineDeriv

/-!
# The line map derivative bounds

The composition bound requires the line map iterated derivatives bounded by a
single quantity raised to the order. Taking the direction norm: order one is
exactly that, and orders two and three vanish, the map being affine.

The vanishing at order three follows from the order-two case by the same
argument one level up: the second iterated derivative is the constant zero
function, so its derivative is zero and the curry isometry carries zero to
zero.

## Main results

- iteratedFDeriv_three_line
- line_deriv_bounds
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The composition bound

`norm_iteratedFDeriv_comp_le` needs the line map's derivatives bounded by
`D ^ i` for `1 ≤ i ≤ 3` with a single `D`. Taking `D = ‖z‖`:

* `i = 1`: the norm is exactly `‖z‖`, by `norm_fderiv_line`;
* `i = 2, 3`: the norm is zero, which is at most `‖z‖ ^ i`.

The third order needs the same vanishing argument as the second; since the
second iterated derivative is identically zero as a function, every higher one
vanishes too.
-/


/-- The second iterated derivative is zero as a function, so higher ones
vanish. -/
theorem iteratedFDeriv_three_line (x z : EuclSpace d) (t : ℝ) :
    iteratedFDeriv ℝ 3 (fun s : ℝ => x + s • z) t = 0 := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedFDeriv_succ_eq_comp_left]
  simp only [Function.comp_apply]
  have hconst : iteratedFDeriv ℝ 2 (fun s : ℝ => x + s • z)
      = Function.const ℝ 0 := by
    funext u
    exact iteratedFDeriv_two_line x z u
  rw [hconst, fderiv_const]
  exact LinearIsometryEquiv.map_zero _

/-- The line map's derivative bounds, in the form the composition bound
wants. -/
theorem line_deriv_bounds (x z : EuclSpace d) (t : ℝ) :
    ∀ i : ℕ, 1 ≤ i → i ≤ 3 →
      ‖iteratedFDeriv ℝ i (fun s : ℝ => x + s • z) t‖ ≤ ‖z‖ ^ i := by
  intro i h1 h3
  interval_cases i
  · rw [norm_fderiv_line]; simp
  · rw [norm_iteratedFDeriv_two_line]; positivity
  · rw [iteratedFDeriv_three_line, norm_zero]; positivity

end

end PLaplacian
