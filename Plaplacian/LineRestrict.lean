/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.SecondOrder
public import Plaplacian.Viscosity

@[expose] public section

/-!
# The multivariate second-order necessary condition

At a local maximum of a twice continuously differentiable function on a
Euclidean space the Hessian is nonpositive as a quadratic form. This is what
consistency of the viscosity definition with classical solutions requires: a
classical solution touching a test function forces an inequality between
Hessians, and degenerate ellipticity then transfers the operator inequality.

The proof restricts to a line through the point and applies the
one-dimensional result of `Plaplacian.SecondOrder`. Three steps:

* `IsLocalMax.along_line`: the restriction attains a local maximum at the
  origin;
* `hasDerivAt_first`: its first derivative is the Frechet derivative applied
  to the direction;
* `hasDerivAt_second`: its second derivative is the Hessian at the direction
  twice.

The third is the `iteratedDeriv` against `iteratedFDeriv` glue identified in
our initial gap audit as the likely friction point of the development. It is
resolved by `ContDiff.fderiv_right`, which gives that the derivative map of a
`C^2` function is itself `C^1`, followed by two applications of the chain rule
and the observation that evaluation at a fixed vector is continuous linear.

## Main results

- `hess_nonpos_of_isLocalMax`
-/

open Set Topology Filter

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-! ### The line map -/

/-- The affine line through `x` in direction `v`. -/
def lineMap (x v : EuclSpace d) : ℝ → EuclSpace d := fun t => x + t • v

@[simp] lemma lineMap_zero (x v : EuclSpace d) : lineMap x v 0 = x := by
  simp [lineMap]

lemma contDiff_lineMap (x v : EuclSpace d) : ContDiff ℝ 2 (lineMap x v) := by
  unfold lineMap; fun_prop

lemma continuous_lineMap (x v : EuclSpace d) : Continuous (lineMap x v) :=
  (contDiff_lineMap x v).continuous

lemma hasDerivAt_lineMap (x v : EuclSpace d) (t : ℝ) :
    HasDerivAt (lineMap x v) v t := by
  unfold lineMap
  simpa using (hasDerivAt_id t).smul_const v |>.const_add x

/-! ### The restriction -/

/-- A local maximum restricts to a local maximum along any line. -/
theorem IsLocalMax.along_line {h : EuclSpace d → ℝ} {x : EuclSpace d}
    (hmax : IsLocalMax h x) (v : EuclSpace d) :
    IsLocalMax (fun t : ℝ => h (lineMap x v t)) 0 := by
  have htend : Tendsto (lineMap x v) (𝓝 (0 : ℝ)) (𝓝 x) := by
    have := (continuous_lineMap x v).tendsto 0
    rwa [lineMap_zero] at this
  have hev := htend.eventually hmax
  rw [IsLocalMax, IsMaxFilter]
  rw [lineMap_zero]
  exact hev

lemma contDiff_restrict {h : EuclSpace d → ℝ} (hh : ContDiff ℝ 2 h)
    (x v : EuclSpace d) :
    ContDiff ℝ 2 (fun t : ℝ => h (lineMap x v t)) :=
  hh.comp (contDiff_lineMap x v)

/-- The first derivative along a line. -/
theorem hasDerivAt_first {h : EuclSpace d → ℝ} (hh : ContDiff ℝ 2 h)
    (x v : EuclSpace d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => h (lineMap x v s))
      (fderiv ℝ h (lineMap x v t) v) t := by
  have h1 : HasFDerivAt h (fderiv ℝ h (lineMap x v t)) (lineMap x v t) :=
    (hh.differentiable (by norm_num) _).hasFDerivAt
  exact h1.comp_hasDerivAt t (hasDerivAt_lineMap x v t)

theorem deriv_first {h : EuclSpace d → ℝ} (hh : ContDiff ℝ 2 h)
    (x v : EuclSpace d) :
    deriv (fun s : ℝ => h (lineMap x v s))
      = fun t => fderiv ℝ h (lineMap x v t) v := by
  funext t
  exact (hasDerivAt_first hh x v t).deriv

/-! ### The second derivative -/

lemma differentiable_fderiv {h : EuclSpace d → ℝ} (hh : ContDiff ℝ 2 h) :
    Differentiable ℝ (fderiv ℝ h) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ h) := hh.fderiv_right (by norm_num)
  exact h1.differentiable (by norm_num)

lemma hasFDerivAt_fderiv {h : EuclSpace d → ℝ} (hh : ContDiff ℝ 2 h)
    (y : EuclSpace d) :
    HasFDerivAt (fderiv ℝ h) (fderiv ℝ (fderiv ℝ h) y) y :=
  (differentiable_fderiv hh y).hasFDerivAt

/-- **The second derivative along a line is the Hessian at the direction
twice.** -/
theorem hasDerivAt_second {h : EuclSpace d → ℝ} (hh : ContDiff ℝ 2 h)
    (x v : EuclSpace d) :
    HasDerivAt (fun t : ℝ => fderiv ℝ h (lineMap x v t) v)
      (fderiv ℝ (fderiv ℝ h) x v v) 0 := by
  have hcomp : HasDerivAt (fun t : ℝ => fderiv ℝ h (lineMap x v t))
      (fderiv ℝ (fderiv ℝ h) x v) 0 := by
    have h1 : HasFDerivAt (fderiv ℝ h)
        (fderiv ℝ (fderiv ℝ h) (lineMap x v 0)) (lineMap x v 0) :=
      hasFDerivAt_fderiv hh _
    have h2 := h1.comp_hasDerivAt 0 (hasDerivAt_lineMap x v 0)
    rw [lineMap_zero] at h2
    exact h2
  have heval : HasFDerivAt (fun L : EuclSpace d →L[ℝ] ℝ => L v)
      (ContinuousLinearMap.apply ℝ ℝ v)
      (fderiv ℝ h (lineMap x v 0)) :=
    (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt
  have hres := heval.comp_hasDerivAt 0 hcomp
  simp only [Function.comp_def, ContinuousLinearMap.apply_apply] at hres
  exact hres

/-! ### The conclusion -/

/-- **The Hessian is nonpositive at a local maximum.** -/
theorem hess_nonpos_of_isLocalMax {h : EuclSpace d → ℝ}
    (hh : ContDiff ℝ 2 h) {x : EuclSpace d} (hmax : IsLocalMax h x)
    (v : EuclSpace d) :
    fderiv ℝ (fderiv ℝ h) x v v ≤ 0 := by
  set g : ℝ → ℝ := fun t => h (lineMap x v t) with hgdef
  have hgC : ContDiff ℝ 2 g := contDiff_restrict hh x v
  have hgmax : IsLocalMax g 0 := IsLocalMax.along_line hmax v
  have hd1 : deriv g = fun t => fderiv ℝ h (lineMap x v t) v :=
    deriv_first hh x v
  have hd2 : deriv (deriv g) 0 = fderiv ℝ (fderiv ℝ h) x v v := by
    rw [hd1]
    exact (hasDerivAt_second hh x v).deriv
  have := IsLocalMax.deriv_deriv_nonpos hgC hgmax
  rwa [hd2] at this

end PLaplacian

end
