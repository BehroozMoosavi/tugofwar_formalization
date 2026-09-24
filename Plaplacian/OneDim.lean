/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.AllOrders

/-!
# The one-dimensional conversion

The composition bound speaks of the flat iterated derivative of a function on
the reals; the Taylor remainder speaks of iterated deriv. The bridge is the
field equivalence, which is a linear isometry, so the norms agree, and the
successor rule unwinds iteratedDeriv into iterated deriv.

## Main results

- norm_iteratedFDeriv_eq_norm_iteratedDeriv
- norm_iteratedFDeriv_eq_abs_iteratedDeriv
- iteratedDeriv_three
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The one-dimensional conversion

The composition bound is stated for `iteratedFDeriv ℝ 3` of a function on the
reals. `exists_bound_deriv_three` speaks of iterated `deriv`. The bridge is
`iteratedFDeriv_eq_equiv_comp`, whose equivalence is a linear isometry, so the
norms agree; and `iteratedDeriv_succ` unwinds `iteratedDeriv` into iterated
`deriv`.
-/


/-- The norms agree, the equivalence being an isometry. -/
theorem norm_iteratedFDeriv_eq_norm_iteratedDeriv (g : ℝ → EuclSpace d)
    (n : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ n g t‖ = ‖iteratedDeriv n g t‖ := by
  rw [iteratedFDeriv_eq_equiv_comp]
  exact LinearIsometryEquiv.norm_map _ _

/-- The scalar version, which is what we need. -/
theorem norm_iteratedFDeriv_eq_abs_iteratedDeriv (g : ℝ → ℝ) (n : ℕ)
    (t : ℝ) :
    ‖iteratedFDeriv ℝ n g t‖ = |iteratedDeriv n g t| := by
  rw [iteratedFDeriv_eq_equiv_comp, Function.comp_apply,
      LinearIsometryEquiv.norm_map]
  exact Real.norm_eq_abs _

/-- `iteratedDeriv 3` as iterated `deriv`. -/
theorem iteratedDeriv_three (g : ℝ → ℝ) :
    iteratedDeriv 3 g = deriv (deriv (deriv g)) := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_succ,
      show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ,
      show (1 : ℕ) = 0 + 1 from rfl, iteratedDeriv_succ,
      iteratedDeriv_zero]

end

end PLaplacian
