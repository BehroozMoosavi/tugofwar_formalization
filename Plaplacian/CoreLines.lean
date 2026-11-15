/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.SubJetAlg

@[expose] public section

/-! # The line arguments at a maximum of the doubled function

Let `(ξ, ζ)` be a local maximum of

  `Ŵ(x, y) = û(x) - v̌(y) - P(x - y) + ⟪p₁, x⟫ + ⟪p₂, y⟫`,

with `(a, X)` a subjet of `û` at `ξ` and `(b, Y)` a superjet of `v̌` at `ζ`.
Each conclusion is the second-order condition at a maximum, `localMax_subJet`,
for a function of one variable built from `Ŵ`.

* **Along the diagonal**, `y ↦ Ŵ(y, y + (ζ - ξ))`: the penalty is constant, and
  the subjet is `(a - b + p₁ + p₂, X - Y)`. Hence `X ≤ Y`, which is the
  inequality the theorem of sums exists to produce, and no matrix inequality
  is needed.

* **In the first variable**, `y ↦ Ŵ(y, ζ)`: the penalty `-P(y - ζ)` is bounded
  below by its first-order polynomial minus `M ‖y - ξ‖²`, a subjet with form
  `-2M I`. Hence `a = g - p₁`, with `g` the penalty gradient at `ξ - ζ`.

* **In the second variable**, symmetrically, `b = g + p₂`.

The penalty is abstract here, assumed only to satisfy an upper Taylor bound
`P(d + k) ≤ P(d) + ⟪g, k⟫ + M ‖k‖²` at `d = ξ - ζ`.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



set_option synthInstance.maxHeartbeats 200000 in
-- The zero form applied twice.
theorem zero_form_apply (v : EuclSpace d) : ((0 : Bilin d) v) v = 0 := by
  simp only [zero_apply]

set_option synthInstance.maxHeartbeats 200000 in
-- A scalar multiple of a form applied twice.
theorem smul_form_apply (c : ℝ) (X : Bilin d) (v : EuclSpace d) :
    ((c • X) v) v = c * (X v) v := by
  simp only [smul_apply, smul_eq_mul]

/-- A local maximum pulls back along a continuous map. -/
theorem isLocalMax_pullback {F : EuclSpace d × EuclSpace d → ℝ}
    {z₀ : EuclSpace d × EuclSpace d} (hmax : IsLocalMax F z₀)
    {φ : EuclSpace d → EuclSpace d × EuclSpace d} {x : EuclSpace d}
    (hφ : Tendsto φ (𝓝 x) (𝓝 z₀)) (hx : φ x = z₀) :
    IsLocalMax (fun y => F (φ y)) x := by
  unfold IsLocalMax IsMaxFilter at hmax ⊢
  filter_upwards [hφ.eventually hmax] with y hy
  rw [hx]
  exact hy

/-- Adding an affine function shifts a subjet's gradient. -/
theorem subJet_add_affine {f : EuclSpace d → ℝ} {x q : EuclSpace d}
    {X : Bilin d} (h : (q, X) ∈ SubJet f x) (p : EuclSpace d) (c : ℝ) :
    (q + p, X) ∈ SubJet (fun y => f y + inner ℝ p y + c) x := by
  intro η hη
  filter_upwards [h η hη] with y hy
  change f x + inner ℝ q (y - x) + (1 / 2) * (X (y - x)) (y - x)
    - η * ‖y - x‖ ^ 2 ≤ f y at hy
  change f x + inner ℝ p x + c + inner ℝ (q + p) (y - x)
    + (1 / 2) * (X (y - x)) (y - x) - η * ‖y - x‖ ^ 2 ≤ f y + inner ℝ p y + c
  have e : inner ℝ p (y - x) = inner ℝ p y - inner ℝ p x := inner_sub_right _ _ _
  rw [inner_add_left]
  linarith

section core

variable {u v P : EuclSpace d → ℝ} {p₁ p₂ ξ ζ a b : EuclSpace d} {X Y : Bilin d}

/-- The doubled function with linear perturbations. -/
def dblW (u v P : EuclSpace d → ℝ) (p₁ p₂ : EuclSpace d)
    (z : EuclSpace d × EuclSpace d) : ℝ :=
  u z.1 - v z.2 - P (z.1 - z.2) + inner ℝ p₁ z.1 + inner ℝ p₂ z.2

/-- **Along the diagonal: `X ≤ Y`.** -/
theorem core_diag (hmax : IsLocalMax (dblW u v P p₁ p₂) (ξ, ζ))
    (hu : (a, X) ∈ SubJet u ξ) (hv : (b, Y) ∈ SuperJet v ζ) :
    QuadLE X Y := by
  set c := ζ - ξ with hc
  -- the restriction to the diagonal line through (ξ, ζ)
  have hφ : Tendsto (fun y : EuclSpace d => (y, y + c)) (𝓝 ξ) (𝓝 (ξ, ζ)) := by
    have h0 : Continuous (fun y : EuclSpace d => (y, y + c)) :=
      continuous_id.prodMk (continuous_id.add continuous_const)
    have := h0.tendsto ξ
    have e : ξ + c = ζ := by rw [hc]; abel
    rw [e] at this
    exact this
  have hφx : (fun y : EuclSpace d => (y, y + c)) ξ = (ξ, ζ) := by
    simp only; rw [hc]; congr 1; abel
  have hgmax := isLocalMax_pullback hmax hφ hφx
  -- its subjet
  have hv' : (b, Y) ∈ SuperJet v (ξ + c) := by
    have e : ξ + c = ζ := by rw [hc]; abel
    rw [e]; exact hv
  have hneg := subJet_comp_add c (subJet_neg_of_superJet hv')
  have hsum := subJet_add hu hneg
  have haff := subJet_add_affine hsum (p₁ + p₂) (-P (ξ - ζ) + inner ℝ p₂ c)
  have hfun : (fun y => (fun y => u y + (fun y => -v y) (y + c)) y
        + inner ℝ (p₁ + p₂) y + (-P (ξ - ζ) + inner ℝ p₂ c))
      = fun y => dblW u v P p₁ p₂ (y, y + c) := by
    funext y
    unfold dblW
    simp only
    have e : y - (y + c) = ξ - ζ := by rw [hc]; abel
    rw [e, inner_add_left, inner_add_right]
    ring
  have hg := subJet_congr hfun haff
  have hcond := (localMax_subJet hgmax hg).2
  intro w
  have h1 := hcond w
  rw [add_form_apply, neg_form_apply, zero_form_apply] at h1
  linarith

/-- **In the first variable: the gradient of `û`.** -/
theorem core_grad_u (hmax : IsLocalMax (dblW u v P p₁ p₂) (ξ, ζ))
    (hu : (a, X) ∈ SubJet u ξ) {g : EuclSpace d} {M : ℝ}
    (hP : ∀ k, P (ξ - ζ + k) ≤ P (ξ - ζ) + inner ℝ g k + M * ‖k‖ ^ 2) :
    a = g - p₁ := by
  have hφ : Tendsto (fun y : EuclSpace d => (y, ζ)) (𝓝 ξ) (𝓝 (ξ, ζ)) :=
    (continuous_id.prodMk continuous_const).tendsto ξ
  have hgmax := isLocalMax_pullback hmax hφ rfl
  -- the penalty term has an exact quadratic lower bound at ξ
  have hpen : (-g, (-2 * M) • idForm d) ∈ SubJet (fun y => -P (y - ζ)) ξ := by
    apply subJet_of_lower
    intro k
    have e : ξ + k - ζ = ξ - ζ + k := by abel
    rw [e, smul_form_apply, idForm_apply, inner_neg_left]
    have := hP k
    linarith
  have hsum := subJet_add hu hpen
  have haff := subJet_add_affine hsum p₁ (-v ζ + inner ℝ p₂ ζ)
  have hfun : (fun y => (fun y => u y + -P (y - ζ)) y + inner ℝ p₁ y
        + (-v ζ + inner ℝ p₂ ζ))
      = fun y => dblW u v P p₁ p₂ (y, ζ) := by
    funext y; unfold dblW; simp only; ring
  have hg := subJet_congr hfun haff
  have hq := (localMax_subJet hgmax hg).1
  have : a = -(-g) - p₁ := by
    have h2 : a + -g + p₁ = 0 := hq
    calc a = (a + -g + p₁) + g - p₁ := by abel
      _ = 0 + g - p₁ := by rw [h2]
      _ = -(-g) - p₁ := by abel
  rw [this, neg_neg]

/-- **In the second variable: the gradient of `v̌`.** -/
theorem core_grad_v (hmax : IsLocalMax (dblW u v P p₁ p₂) (ξ, ζ))
    (hv : (b, Y) ∈ SuperJet v ζ) {g : EuclSpace d} {M : ℝ}
    (hP : ∀ k, P (ξ - ζ + k) ≤ P (ξ - ζ) + inner ℝ g k + M * ‖k‖ ^ 2) :
    b = g + p₂ := by
  have hφ : Tendsto (fun y : EuclSpace d => (ξ, y)) (𝓝 ζ) (𝓝 (ξ, ζ)) :=
    (continuous_const.prodMk continuous_id).tendsto ζ
  have hgmax := isLocalMax_pullback hmax hφ rfl
  have hneg := subJet_neg_of_superJet hv
  -- the penalty term, now in the second variable
  have hpen : (g, (-2 * M) • idForm d) ∈ SubJet (fun y => -P (ξ - y)) ζ := by
    apply subJet_of_lower
    intro k
    have e : ξ - (ζ + k) = ξ - ζ + -k := by abel
    rw [e, smul_form_apply, idForm_apply]
    have := hP (-k)
    rw [inner_neg_right, norm_neg] at this
    linarith
  have hsum := subJet_add hneg hpen
  have haff := subJet_add_affine hsum p₂ (u ξ + inner ℝ p₁ ξ)
  have hfun : (fun y => (fun y => -v y + -P (ξ - y)) y + inner ℝ p₂ y
        + (u ξ + inner ℝ p₁ ξ))
      = fun y => dblW u v P p₁ p₂ (ξ, y) := by
    funext y; unfold dblW; simp only; ring
  have hg := subJet_congr hfun haff
  have hq := (localMax_subJet hgmax hg).1
  have h2 : -b + g + p₂ = 0 := hq
  calc b = b + (-b + g + p₂) := by rw [h2, add_zero]
    _ = g + p₂ := by abel

end core

end

end PLaplacian
