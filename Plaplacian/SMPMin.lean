/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.SMP

@[expose] public section

/-! # The strong minimum principle

The negation of a supersolution of `-Δᴺₚ u = 0` is a subsolution, so the
strong maximum principle gives the strong minimum principle.

* **Regular case.** A local maximum of `-V - φ` is a local minimum of
  `V - (-φ)`; the gradient of `-φ` is nonzero when that of `φ` is, and the
  operator is odd (`normPLapOf_neg`).
* **Singular case.** The Hessian of `-φ` is minus that of `φ`, and
  `λ_min(-X) = -λ_max(X)` (from `lamMax_neg` applied to `-X`), so
  `viscFUpper p (-X) = -viscFLower p X`.
-/

open Set Topology Filter Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- The gradient of a negated function vanishes when the original does. -/
theorem gradient_neg_eq_zero {φ : EuclSpace d → ℝ} {x : EuclSpace d}
    (h : gradient φ x = 0) : gradient (fun y => -φ y) x = 0 := by
  unfold gradient at h ⊢
  change (InnerProductSpace.toDual ℝ (EuclSpace d)).symm (fderiv ℝ (-φ) x) = 0
  rw [fderiv_neg, map_neg, h, neg_zero]

/-- A local maximum of `-V - φ` is a local minimum of `V - (-φ)`. -/
theorem isLocalMin_of_neg {V φ : EuclSpace d → ℝ} {x₀ : EuclSpace d}
    (h : IsLocalMax (fun y => (fun y => -V y) y - φ y) x₀) :
    IsLocalMin (fun y => V y - (fun y => -φ y) y) x₀ := by
  have hm : ∀ᶠ y in 𝓝 x₀, -V y - φ y ≤ -V x₀ - φ x₀ := h
  refine hm.mono fun y hy => ?_
  change V x₀ - -φ x₀ ≤ V y - -φ y
  linarith

/-- **The negation of a supersolution is a subsolution.** -/
theorem IsViscositySupersolution.neg {p : ℝ} {Ω : Set (EuclSpace d)}
    {V : EuclSpace d → ℝ} (h : IsViscositySupersolution p Ω (fun _ => 0) V) :
    IsViscositySubsolution p Ω (fun _ => 0) (fun y => -V y) where
  usc := by
    intro x hx c hc
    have hev := h.lsc x hx (-c) (by linarith)
    exact hev.mono fun y hy => by linarith
  regular := by
    intro φ hφ x₀ hx₀ hmax hg
    have hmin := isLocalMin_of_neg hmax
    have h1 := h.regular (fun y => -φ y) hφ.neg x₀ hx₀ hmin (gradient_neg_ne_zero hg)
    change (0 : ℝ) ≤ _ at h1
    change viscF p (gradient φ x₀) (hess φ x₀) ≤ (0 : ℝ)
    rw [viscF_eq_neg] at h1 ⊢
    unfold hess at h1 ⊢
    rw [normPLapOf_neg] at h1
    linarith
  singular := by
    intro φ hφ x₀ hx₀ hmax hg
    have hmin := isLocalMin_of_neg hmax
    have h1 := h.singular (fun y => -φ y) hφ.neg x₀ hx₀ hmin (gradient_neg_eq_zero hg)
    change (0 : ℝ) ≤ _ at h1
    change viscFLower p (hess φ x₀) ≤ (0 : ℝ)
    unfold hess at h1 ⊢
    rw [hess_neg] at h1
    unfold viscFUpper at h1
    unfold viscFLower
    rw [laplacianOf_neg] at h1
    set X := fderiv ℝ (fderiv ℝ φ) x₀ with hX
    have hl : lamMax (-(-X)) = -lamMin (-X) := lamMax_neg (-X)
    have e : lamMax (-(-X)) = lamMax X := congrArg lamMax (neg_neg X)
    have hmin' : lamMin (-X) = -lamMax X := by linarith
    change (0 : ℝ) ≤ - -laplacianOf X - (p - 2) * lamMin (-X) at h1
    rw [hmin'] at h1
    linarith

/-- **The strong minimum principle on a ball.** -/
theorem smp_ball_min (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p) {Ω : Set (EuclSpace d)}
    {V : EuclSpace d → ℝ} (hsup : IsViscositySupersolution p Ω (fun _ => 0) V)
    {x : EuclSpace d} {R : ℝ} (hR : 0 < R) (hball : ball x R ⊆ Ω)
    (hmin : ∀ y ∈ ball x R, V x ≤ V y) :
    ∀ y ∈ ball x (R / 3), V y = V x := by
  have key := smp_ball hd hp hsup.neg hR hball (fun y hy => neg_le_neg (hmin y hy))
  intro y hy
  exact neg_inj.1 (key y hy)

end

end PLaplacian
