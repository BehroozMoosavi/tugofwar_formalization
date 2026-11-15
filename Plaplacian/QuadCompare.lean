/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.SupUpper

@[expose] public section

/-!
# Comparing the quadratic terms

The sandwich on the supremum leaves a gap: one side carries the quadratic form
at the shifted point, the other at the maximizer. The bilinear identity

  X u u minus X v v equals X of u minus v at u, plus X at v of u minus v,

turns the difference into two terms each bounded by the operator norm, giving
the estimate by the norm of X times the norm of u minus v times the sum of the
norms of u and v.

With both arguments of norm at most epsilon and their difference of order
epsilon to the three halves from the localization, the gap is of order epsilon
to the five halves, which is smaller than epsilon squared and so does not
disturb the expansion.

## Main results

- quad_sub_quad: the bilinear identity.
- quad_diff_bound: the estimate.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## Comparing the two quadratic terms

The sandwich leaves a gap: one side has `D²φ x (ε ν, ε ν)` and the other
`D²φ x (y - x, y - x)`. The localization bounds `‖(y - x) - ε ν‖`, and a
bilinear form's values at two nearby arguments differ by a controlled amount.

The identity is
  `X u u - X v v = X (u - v) u + X v (u - v)`,
so the difference is bounded by `‖X‖ ‖u - v‖ (‖u‖ + ‖v‖)`.
-/


/-- The bilinear difference identity. -/
theorem quad_sub_quad (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ)
    (u v : EuclSpace d) :
    X u u - X v v = X (u - v) u + X v (u - v) := by
  have h1 : X (u - v) u = X u u - X v u := by
    rw [map_sub]
    rfl
  have h2 : X v (u - v) = X v u - X v v := by
    rw [map_sub]
  rw [h1, h2]
  ring

/-- **The quadratic terms differ by a controlled amount.** -/
theorem quad_diff_bound (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ)
    (u v : EuclSpace d) :
    |X u u - X v v| ≤ ‖X‖ * ‖u - v‖ * (‖u‖ + ‖v‖) := by
  rw [quad_sub_quad X u v]
  have h1 : |X (u - v) u| ≤ ‖X‖ * ‖u - v‖ * ‖u‖ := by
    have a1 : ‖X (u - v) u‖ ≤ ‖X (u - v)‖ * ‖u‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have a2 : ‖X (u - v)‖ ≤ ‖X‖ * ‖u - v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have hu : (0:ℝ) ≤ ‖u‖ := norm_nonneg u
    simp only [Real.norm_eq_abs] at a1
    nlinarith [a1, a2, hu, norm_nonneg (X (u - v))]
  have h2 : |X v (u - v)| ≤ ‖X‖ * ‖v‖ * ‖u - v‖ := by
    have a1 : ‖X v (u - v)‖ ≤ ‖X v‖ * ‖u - v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have a2 : ‖X v‖ ≤ ‖X‖ * ‖v‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have huv : (0:ℝ) ≤ ‖u - v‖ := norm_nonneg _
    simp only [Real.norm_eq_abs] at a1
    nlinarith [a1, a2, huv, norm_nonneg (X v)]
  have h3 : |X (u - v) u + X v (u - v)|
      ≤ |X (u - v) u| + |X v (u - v)| := abs_add_le _ _
  nlinarith [h1, h2, h3]

end

end PLaplacian
