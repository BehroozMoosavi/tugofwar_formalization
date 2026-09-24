/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.OneDim

/-!
# The cubic Taylor bound

The third derivative of the restriction of a test function to a line is
bounded by a constant times the cube of the direction, with the constant
depending only on the function, the base point and the radius.

This is what the Taylor remainder needs for a rate. The bound proved earlier
asserts only the existence of a constant, with the dependence on the direction
hidden; here it is explicit, obtained by bounding the composition rather than
the pointwise identity, so that the three factors of the direction appear
through the derivative of the line map.

The route uses the flat derivative representation throughout, which is the
only one admitting the operator norm. Together with the uniform constant
across orders and the one-dimensional conversion, the composition bound gives
the cube.

## Main results

- norm_iteratedFDeriv_three_comp
- deriv_three_cubic_bound
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The cubic Taylor bound

Composing. For `z` in the ball and `t` in the unit interval:

* `exists_bound_all_orders` gives a constant `C` bounding `φ`'s derivatives up
  to order three on the ball;
* `norm_iteratedFDeriv_three_comp` turns that into
  `‖iteratedFDeriv ℝ 3 (φ ∘ line) t‖ ≤ 6 C ‖z‖³`;
* `norm_iteratedFDeriv_eq_abs_iteratedDeriv` and `iteratedDeriv_three`
  restate it as `|deriv³ (φ ∘ line) t| ≤ 6 C ‖z‖³`.

That is the hypothesis `taylor_two_bounded` consumes, with the cubic
dependence now explicit: the Taylor error is at most `C ‖z‖³`.
-/


/-- The cubic bound on the composition, from norm_iteratedFDeriv_comp_le. -/
theorem norm_iteratedFDeriv_three_comp {φ : EuclSpace d → ℝ}
    (hφ : ContDiff ℝ 3 φ) (x z : EuclSpace d) (t : ℝ) {C : ℝ}
    (hC : ∀ i ≤ 3, ‖iteratedFDeriv ℝ i φ (x + t • z)‖ ≤ C) :
    ‖iteratedFDeriv ℝ 3 (φ ∘ (fun s : ℝ => x + s • z)) t‖
      ≤ 6 * C * ‖z‖ ^ 3 := by
  have h := norm_iteratedFDeriv_comp_le hφ (contDiff_line x z 3)
    (le_refl (3 : WithTop ℕ∞)) t hC (line_deriv_bounds x z t)
  have hfact : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hfact] at h
  exact h

/-- The line composition, as a function. -/
theorem comp_line_eq (φ : EuclSpace d → ℝ) (x z : EuclSpace d) :
    (φ ∘ (fun s : ℝ => x + s • z)) = fun s : ℝ => φ (x + s • z) := rfl

/-- **The third derivative of the restriction, bounded cubically.** -/
theorem deriv_three_cubic_bound {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x : EuclSpace d) (ε : ℝ) :
    ∃ C : ℝ, ∀ z : EuclSpace d, ‖z‖ ≤ ε → ∀ t : ℝ,
      x + t • z ∈ closedBall x ε →
      |deriv (deriv (deriv (fun s : ℝ => φ (x + s • z)))) t|
        ≤ 6 * C * ‖z‖ ^ 3 := by
  obtain ⟨C, hC⟩ := exists_bound_all_orders hφ x ε
  refine ⟨C, fun z hz t ht => ?_⟩
  have hbd := norm_iteratedFDeriv_three_comp hφ x z t (hC _ ht)
  rw [comp_line_eq] at hbd
  rw [← iteratedDeriv_three]
  rw [← norm_iteratedFDeriv_eq_abs_iteratedDeriv]
  exact hbd

end

end PLaplacian
