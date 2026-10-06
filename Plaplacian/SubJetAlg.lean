/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.QuadForms

/-! # An algebra of subjets

The line arguments at a Jensen point all reduce to the second-order condition
at a maximum, `localMax_subJet`, applied to a function of one variable built
from the doubled function. Its subjet is assembled from pieces: the subjet of
the sup-convolution, the negated superjet of the inf-convolution, linear terms,
and an exact quadratic lower bound for the penalty. This file proves the rules
that assemble them.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



section rules

variable {f g : EuclSpace d → ℝ} {x q₁ q₂ : EuclSpace d} {X₁ X₂ : Bilin d}

set_option synthInstance.maxHeartbeats 200000 in
-- The sum of two forms, applied twice, needs instance search on iterated
-- continuous linear maps.
theorem add_form_apply (X₁ X₂ : Bilin d) (v : EuclSpace d) :
    ((X₁ + X₂) v) v = (X₁ v) v + (X₂ v) v := by
  simp only [add_apply]

set_option synthInstance.maxHeartbeats 200000 in
-- As above, for negation.
theorem neg_form_apply (X : Bilin d) (v : EuclSpace d) :
    ((-X) v) v = -((X v) v) := by
  simp only [neg_apply]

/-- **Subjets add.** -/
theorem subJet_add (h₁ : (q₁, X₁) ∈ SubJet f x) (h₂ : (q₂, X₂) ∈ SubJet g x) :
    (q₁ + q₂, X₁ + X₂) ∈ SubJet (fun y => f y + g y) x := by
  intro η hη
  filter_upwards [h₁ (η / 2) (by positivity), h₂ (η / 2) (by positivity)]
    with y hy₁ hy₂
  change f x + inner ℝ q₁ (y - x) + (1 / 2) * (X₁ (y - x)) (y - x)
    - η / 2 * ‖y - x‖ ^ 2 ≤ f y at hy₁
  change g x + inner ℝ q₂ (y - x) + (1 / 2) * (X₂ (y - x)) (y - x)
    - η / 2 * ‖y - x‖ ^ 2 ≤ g y at hy₂
  change f x + g x + inner ℝ (q₁ + q₂) (y - x)
    + (1 / 2) * ((X₁ + X₂) (y - x)) (y - x) - η * ‖y - x‖ ^ 2 ≤ f y + g y
  rw [inner_add_left, add_form_apply]
  linarith

/-- **A superjet, negated, is a subjet of the negated function.** -/
theorem subJet_neg_of_superJet (h : (q₁, X₁) ∈ SuperJet f x) :
    (-q₁, -X₁) ∈ SubJet (fun y => -f y) x := by
  intro η hη
  filter_upwards [h η hη] with y hy
  change f y ≤ f x + inner ℝ q₁ (y - x) + (1 / 2) * (X₁ (y - x)) (y - x)
    + η * ‖y - x‖ ^ 2 at hy
  change -f x + inner ℝ (-q₁) (y - x) + (1 / 2) * ((-X₁) (y - x)) (y - x)
    - η * ‖y - x‖ ^ 2 ≤ -f y
  rw [inner_neg_left, neg_form_apply]
  linarith

/-- **A subjet, negated, is a superjet of the negated function.** -/
theorem superJet_neg_of_subJet (h : (q₁, X₁) ∈ SubJet f x) :
    (-q₁, -X₁) ∈ SuperJet (fun y => -f y) x := by
  intro η hη
  filter_upwards [h η hη] with y hy
  change f x + inner ℝ q₁ (y - x) + (1 / 2) * (X₁ (y - x)) (y - x)
    - η * ‖y - x‖ ^ 2 ≤ f y at hy
  change -f y ≤ -f x + inner ℝ (-q₁) (y - x) + (1 / 2) * ((-X₁) (y - x)) (y - x)
    + η * ‖y - x‖ ^ 2
  rw [inner_neg_left, neg_form_apply]
  linarith

/-- **Subjets translate.** -/
theorem subJet_comp_add (c : EuclSpace d) (h : (q₁, X₁) ∈ SubJet f (x + c)) :
    (q₁, X₁) ∈ SubJet (fun y => f (y + c)) x := by
  intro η hη
  have hT : Tendsto (fun y : EuclSpace d => y + c) (𝓝 x) (𝓝 (x + c)) :=
    (continuous_id.add continuous_const).tendsto x
  filter_upwards [hT.eventually (h η hη)] with y hy
  change f (x + c) + inner ℝ q₁ (y + c - (x + c))
    + (1 / 2) * (X₁ (y + c - (x + c))) (y + c - (x + c))
    - η * ‖y + c - (x + c)‖ ^ 2 ≤ f (y + c) at hy
  change f (x + c) + inner ℝ q₁ (y - x) + (1 / 2) * (X₁ (y - x)) (y - x)
    - η * ‖y - x‖ ^ 2 ≤ f (y + c)
  have e : y + c - (x + c) = y - x := by abel
  rw [e] at hy
  exact hy

/-- **An exact quadratic lower bound gives a subjet.** -/
theorem subJet_of_lower {Z : Bilin d}
    (h : ∀ k : EuclSpace d, g x + inner ℝ q₁ k + (1 / 2) * (Z k) k ≤ g (x + k)) :
    (q₁, Z) ∈ SubJet g x := by
  intro η hη
  refine Eventually.of_forall (fun y => ?_)
  change g x + inner ℝ q₁ (y - x) + (1 / 2) * (Z (y - x)) (y - x)
    - η * ‖y - x‖ ^ 2 ≤ g y
  have h1 := h (y - x)
  have e : x + (y - x) = y := by abel
  rw [e] at h1
  have h2 : 0 ≤ η * ‖y - x‖ ^ 2 := by positivity
  linarith

/-- A linear function has the subjet `(p, 0)`. -/
theorem subJet_inner (p : EuclSpace d) :
    (p, (0 : Bilin d)) ∈ SubJet (fun y => inner ℝ p y) x := by
  apply subJet_of_lower
  intro k
  rw [inner_add_right]
  simp

/-- A constant has the subjet `(0, 0)`. -/
theorem subJet_const (c : ℝ) :
    ((0 : EuclSpace d), (0 : Bilin d)) ∈ SubJet (fun _ => c) x := by
  apply subJet_of_lower
  intro k
  simp

end rules

/-- **Subjet congruence**: a subjet of `f` is one of any function equal to it. -/
theorem subJet_congr {f g : EuclSpace d → ℝ} (hfg : f = g) {x q : EuclSpace d}
    {X : Bilin d} (h : (q, X) ∈ SubJet f x) : (q, X) ∈ SubJet g x := by
  subst hfg; exact h

end

end PLaplacian
