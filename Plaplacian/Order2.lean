/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.HessCont

@[expose] public section

/-! ## One-dimensional Taylor at order two

Both earlier routes hit the same obstruction: composing derivatives *through*
the space of bilinear maps fails, since that space carries
`ContinuousLinearMap.topologicalSpace` rather than the metric topology. The
second derivative worked only because its intermediate space is one level
down, where the instances happen to align.

This route never leaves the reals. Apply the one-dimensional Taylor theorem at
order **two** to `h t = φ (lineMap x z t)`, which is `C³` in `t` when `φ` is
`C³`; the remainder is then `O(t³)` directly, with no multivariate
composition.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- The line map is smooth to any order. -/
theorem contDiff_lineMap_three (x z : EuclSpace d) :
    ContDiff ℝ 3 (lineMap x z) := by
  unfold lineMap
  fun_prop

/-- The restriction is `C³` when `φ` is. -/
theorem contDiff_restrict_three {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (x z : EuclSpace d) :
    ContDiff ℝ 3 (fun t : ℝ => φ (lineMap x z t)) :=
  hφ.comp (contDiff_lineMap_three x z)

/-- The inner iterated derivative agrees with the plain one on a
neighbourhood, at order two. -/
theorem iteratedDerivWithin_two_eventuallyEq (g : ℝ → ℝ) {a b t : ℝ}
    (ht : t ∈ Ioo (min a b) (max a b)) :
    iteratedDerivWithin 2 g (uIcc a b) =ᶠ[nhds t] deriv (deriv g) := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact iteratedDerivWithin_two_eq g hs

/-- **The order-three translation.** -/
theorem iteratedDerivWithin_three_eq (g : ℝ → ℝ) {a b t : ℝ}
    (ht : t ∈ Ioo (min a b) (max a b)) :
    iteratedDerivWithin 3 g (uIcc a b) t = deriv (deriv (deriv g)) t := by
  rw [show (3 : Nat) = 2 + 1 from rfl, iteratedDerivWithin_succ]
  rw [derivWithin_of_mem_nhds (uIcc_mem_nhds ht)]
  exact (iteratedDerivWithin_two_eventuallyEq g ht).deriv_eq

/-- **The Taylor polynomial at order two.** -/
theorem taylorWithinEval_two (g : ℝ → ℝ) (s : Set ℝ) (x₀ x : ℝ) :
    taylorWithinEval g 2 s x₀ x
      = g x₀ + (x - x₀) * iteratedDerivWithin 1 g s x₀
        + (x - x₀) ^ 2 / 2 * iteratedDerivWithin 2 g s x₀ := by
  rw [show (2 : Nat) = 1 + 1 from rfl, taylorWithinEval_succ,
      taylorWithinEval_one]
  simp only [Nat.factorial, Nat.cast_one, smul_eq_mul]
  ring

end

end PLaplacian
