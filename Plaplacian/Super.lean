/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.NegOp

/-!
# The supersolution inequality in the regular case

At a strict minimum of the lower relaxed limit minus a bounded C three test
function with nonvanishing gradient, the normalized p-Laplacian of the test
function is nonpositive.

Obtained from the subsolution by transport. A strict minimum of the lower
relaxed limit minus the test function is a strict maximum of the upper relaxed
limit of the negated family minus the negated test function; the negated
family is p-harmonious, the operator being odd; and the normalized
p-Laplacian flips sign under negation of the test function. No part of the
regular argument is repeated.

## Main results

- laplacianOf_neg, normPLapOf_neg
- regular_supsol
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The supersolution inequality in the regular case

By transport from the subsolution. A strict minimum of the lower relaxed limit
minus the test function is a strict maximum of the upper relaxed limit of the
negated family minus the negated test function, since the lower limit is minus
the upper limit of the negation. The negated family is `p`-harmonious with
negated data, the operator being odd. So the subsolution inequality applies to
the negations, and the normalized `p`-Laplacian, which flips sign when the
test function is negated, gives the supersolution inequality.

No part of the regular argument is repeated: the supersolution is the
subsolution read through a negation.
-/

/-- The Laplacian of a negated bilinear form. -/
theorem laplacianOf_neg (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) :
    laplacianOf (-X) = - laplacianOf X := by
  unfold laplacianOf
  simp [Finset.sum_neg_distrib]

/-- **The normalized `p`-Laplacian flips sign under negation.** -/
theorem normPLapOf_neg (p : ℝ) (φ : EuclSpace d → ℝ) (x : EuclSpace d) :
    normPLapOf p (gradient (fun y => -φ y) x)
        (fderiv ℝ (fderiv ℝ (fun y => -φ y)) x)
      = - normPLapOf p (gradient φ x) (fderiv ℝ (fderiv ℝ φ) x) := by
  unfold normPLapOf
  rw [infLaplacianOf_neg, hess_neg, laplacianOf_neg]
  ring

/-- **The regular-case supersolution inequality.** -/
theorem regular_supsol [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε))
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ) (hφb : BddMeas φ)
    {B : ℝ} (hB : ∀ y, |φ y| ≤ B)
    {x₀ : EuclSpace d} {r : ℝ} (hr : 0 < r) (hΩ : closedBall x₀ r ⊆ Ω)
    (hmin : ∀ w ∈ closedBall x₀ r, w ≠ x₀ →
      lbar u x₀ - φ x₀ < lbar u w - φ w)
    (hx₀ : gradient φ x₀ ≠ 0) :
    normPLapOf p (gradient φ x₀) (fderiv ℝ (fderiv ℝ φ) x₀) ≤ 0 := by
  -- the negated family and test function
  have hCn : ∀ ε y, |(fun ε y => -u ε y) ε y| ≤ C := by
    intro ε y; simp only; rw [abs_neg]; exact hC ε y
  have hun : ∀ ε > 0, IsPHarmonious p ε Ω (fun y => -F y)
      ((fun ε y => -u ε y) ε) :=
    fun ε hε => isPHarmonious_neg (hu ε hε)
  have hBn : ∀ y, |(fun y => -φ y) y| ≤ B := by
    intro y; simp only; rw [abs_neg]; exact hB y
  -- the strict minimum becomes a strict maximum of the negations
  have hstrict : IsStrictMaxOn
      (fun w => ubar (fun ε y => -u ε y) w - (fun y => -φ y) w) x₀ r := by
    intro w hw hne
    have h1 := lbar_eq_neg_ubar_neg u w
    have h2 := lbar_eq_neg_ubar_neg u x₀
    have h3 := hmin w hw hne
    simp only
    linarith [h1, h2, h3]
  -- the subsolution inequality for the negations
  have h := regular_subsol hd hp hpd hCn hun (contDiff_neg' hφ)
    (bddMeas_neg hφb) hBn hr hΩ hstrict (gradient_neg_ne_zero hx₀)
  rw [normPLapOf_neg] at h
  linarith [h]

end

end PLaplacian
