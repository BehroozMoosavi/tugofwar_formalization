import Mathlib
import Plaplacian.LineRestrict

open Set Topology Filter Asymptotics

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## Route 3: reduce to one dimension

Better than either route in the plan. Set `g t = φ (x + t • z)`. Then
`Plaplacian.LineRestrict` already gives

  `g' t = Dφ (x + t z) z`      (`hasDerivAt_first`)
  `g'' 0 = D²φ x (z, z)`        (`hasDerivAt_second`)

and the one-dimensional Taylor theorem with Lagrange remainder gives
`ξ ∈ (0,1)` with

  `φ (x + z) = φ x + Dφ x z + (1/2) D²φ (x + ξ z) (z, z)`.

The error against `(1/2) D²φ x (z,z)` is then
`(1/2) [D²φ (x + ξ z) - D²φ x] (z,z)`, which is `o(‖z‖²)` because `D²φ` is
continuous and `‖(z,z)‖ = ‖z‖²`.

This uses the one-dimensional API, which exists, instead of the multivariable
approximation API, which does not.
-/

/-! ### The glue we need -/


/-- The restriction is `C²` along the line; already available. -/
example (φ : EuclSpace d → ℝ) (hφ : ContDiff ℝ 2 φ) (x z : EuclSpace d) :
    ContDiff ℝ 2 (fun t : ℝ => φ (lineMap x z t)) :=
  contDiff_restrict hφ x z

/-- Its first derivative, already available. -/
example (φ : EuclSpace d → ℝ) (hφ : ContDiff ℝ 2 φ) (x z : EuclSpace d)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (lineMap x z s))
      (fderiv ℝ φ (lineMap x z t) z) t :=
  hasDerivAt_first hφ x z t

/-- The second derivative at an arbitrary point of the line, which we need for
the remainder. `hasDerivAt_second` gives it at `0`; the general point follows
by translating the base point. -/
example (φ : EuclSpace d → ℝ) (hφ : ContDiff ℝ 2 φ) (x z : EuclSpace d)
    (t : ℝ) :
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

/-- Continuity of the Hessian, needed for the final `o` estimate. -/
example (φ : EuclSpace d → ℝ) (hφ : ContDiff ℝ 2 φ) :
    Continuous (fun y => fderiv ℝ (fderiv ℝ φ) y) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
  exact h1.continuous_fderiv (by norm_num)

end

end PLaplacian
