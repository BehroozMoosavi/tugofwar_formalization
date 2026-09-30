/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.LocalCmp

/-!
# Second-order Taylor with a little-o remainder, along a line

The one-dimensional Taylor theorem with a little-o remainder, applied to the
restriction of a test function to a line, gives the estimate along each
direction for a function of class C two.

This sharpens the earlier finding on Mathlib's Taylor API. It is not that the
library lacks remainder estimates: it is that every one of them is
one-dimensional. Both the Lagrange form and the little-o form take functions
on the reals; the several-variable interface carries derivative towers and no
approximation. The line restriction is therefore not a workaround but the
intended route, and it is the third time in this development that reducing to
a line has been the way through.

What this does not yet give is uniformity across directions: the little-o
constant depends on the direction. Obtaining that needs compactness of the
sphere and is the substance of reducing the test-function class from C three
to C two.

## Main results

- contDiffOn_restrict_two
- taylor_littleO_line
-/

open Set Topology Filter MeasureTheory Metric Asymptotics

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # Second-order Taylor with a little-o remainder, along a line

`taylor_isLittleO` supplies the remainder in one dimension. Applied to the
restriction of a test function to a line, it gives the little-o estimate along
each direction.

This sharpens our earlier finding. It is not that Mathlib lacks remainder
estimates: it is that every one of them is one-dimensional. Both
`taylor_mean_remainder_lagrange` and `taylor_isLittleO` take functions on the
reals. The several-variable API carries derivative towers and no
approximation.
-/


/-- The restriction of a `C²` function to a line is `C²` on any convex set. -/
theorem contDiffOn_restrict_two {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x z : EuclSpace d) (s : Set ℝ) :
    ContDiffOn ℝ 2 (fun t : ℝ => φ (x + t • z)) s := by
  have h : ContDiff ℝ 2 (fun t : ℝ => φ (x + t • z)) := by
    have hline : ContDiff ℝ 2 (fun t : ℝ => x + t • z) := by fun_prop
    exact hφ.comp hline
  exact h.contDiffOn

/-- **The little-o remainder along a line.** -/
theorem taylor_littleO_line {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x z : EuclSpace d) :
    (fun t : ℝ => φ (x + t • z)
        - taylorWithinEval (fun s : ℝ => φ (x + s • z)) 2 univ 0 t)
      =o[nhdsWithin 0 univ] (fun t : ℝ => (t - 0) ^ 2) := by
  refine taylor_isLittleO (E := ℝ) (n := 2)
    (f := fun s : ℝ => φ (x + s • z)) (x₀ := 0) (s := univ)
    convex_univ (Set.mem_univ 0) ?_
  exact contDiffOn_restrict_two hφ x z univ

end

end PLaplacian
