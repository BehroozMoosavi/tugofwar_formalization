/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.NullImage

/-! # Almost every point is good

Let `J` be the proximal map of a convex `f`.

* `N`, where `J` is not differentiable, is null by Rademacher's theorem, `J`
  being one-Lipschitz.
* `S`, where `J` is differentiable with singular derivative, has null image by
  the area formula.
* `J(N)` is null, since `J` is Lipschitz.

So `J(N) ∪ J(S)` is null. For `x` outside it, `y = x + p`, with `p` the chosen
subgradient at `x`, has `J(y) = x`; and `y ∉ N`, `y ∉ S`, so `J` is
differentiable at `y` with invertible derivative. That is the input to the
linear approximation of the subgradients.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



section good

variable {f : EuclSpace d → ℝ}

/-- **The non-differentiability set of the proximal map is null.** -/
theorem prox_nondiff_null (hf : ConvexOn ℝ univ f) :
    (volume : Measure (EuclSpace d)) {y | ¬ DifferentiableAt ℝ (proxMap f) y} = 0 := by
  have h := (prox_lipschitz hf).ae_differentiableAt (μ := (volume : Measure (EuclSpace d)))
  exact ae_iff.1 h

/-- **The image of the singular set is null**, by the area formula. -/
theorem prox_singular_image_null (_hf : ConvexOn ℝ univ f) :
    (volume : Measure (EuclSpace d))
      (proxMap f '' {y | DifferentiableAt ℝ (proxMap f) y ∧
        (fderiv ℝ (proxMap f) y).det = 0}) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (f' := fun y => fderiv ℝ (proxMap f) y)
  · intro y hy
    exact hy.1.hasFDerivAt.hasFDerivWithinAt
  · intro y hy
    exact hy.2

/-- **The bad set is null.** -/
theorem prox_bad_null (hf : ConvexOn ℝ univ f) :
    (volume : Measure (EuclSpace d))
      (proxMap f '' {y | ¬ DifferentiableAt ℝ (proxMap f) y} ∪
        proxMap f '' {y | DifferentiableAt ℝ (proxMap f) y ∧
          (fderiv ℝ (proxMap f) y).det = 0}) = 0 :=
  measure_union_null (lipschitz_image_null (prox_lipschitz hf) (prox_nondiff_null hf))
    (prox_singular_image_null hf)

/-- **Almost every point is good**: it is the proximal point of a point where
the proximal map is differentiable with invertible derivative, the difference
being a subgradient. -/
theorem ae_good (hf : ConvexOn ℝ univ f) :
    ∀ᵐ x ∂(volume : Measure (EuclSpace d)), ∃ y,
      proxMap f y = x ∧ DifferentiableAt ℝ (proxMap f) y ∧
      (fderiv ℝ (proxMap f) y).det ≠ 0 ∧ IsSubgrad f x (y - x) := by
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) (prox_bad_null hf)
  simp only [Set.mem_ofPred_eq, not_exists, not_and] at hx
  set y := x + subgradSel f x with hy
  have hJy : proxMap f y = x := prox_surj hf x
  have hsub : IsSubgrad f x (y - x) := by
    have e : y - x = subgradSel f x := by rw [hy]; abel
    rw [e]; exact subgradSel_spec hf x
  by_cases hd : DifferentiableAt ℝ (proxMap f) y
  · right
    refine ⟨y, ⟨hd, ?_⟩, hJy⟩
    by_contra hdet
    exact hx y hJy hd hdet hsub
  · left
    exact ⟨y, hd, hJy⟩

end good

end

end PLaplacian
