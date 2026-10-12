/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Step2

/-! # Semiconcavity of `ψ(V)`, and supersolution jets from `-V`

**Semiconcavity.** A function with a lower support of uniform constant `L` at
every point is semiconvex with constant `L`: adding `(L/2)‖·‖²` gives a
subgradient everywhere, and a function with a subgradient everywhere is convex.
For `-W`, `W = V - η V²`, the support comes from the upper support of `V` and
the exact identity `ψ(s) - ψ(t) = ψ'(t)(s - t) - η(s - t)²`, with
`0 ≤ ψ'(V) = 1 - 2ηV ≤ C_c`; the constant is `C_c λ`.

**Jets.** The regularized supersolution `V` is minus a sup-convolution, so what
is known directly is that superjets of `-V` satisfy the subsolution
inequality. The second step needs subjets of `V`: the conversion is
`(q, X) ↦ ((-1) • q, (-1) • X)`, with `viscF p ((-1) • q) ((-1) • X) = -viscF p q X`.
Scalar multiplication by `-1` is used rather than negation of forms.
-/

open Set Topology Filter Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-! ## Semiconvexity from uniform lower supports -/

/-- **Uniform lower supports give semiconvexity.** -/
theorem semiconvex_of_supports {L : ℝ} {f : EuclSpace d → ℝ}
    (h : ∀ x, ∃ g, ∀ y, f x + inner ℝ g (y - x) - L / 2 * ‖y - x‖ ^ 2 ≤ f y) :
    SemiconvexWith L f := by
  refine ⟨convex_univ, fun y₁ _ y₂ _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set z := a • y₁ + b • y₂ with hz
  obtain ⟨g, hg⟩ := h z
  set G := g + L • z with hG
  -- the subgradient inequality for f + (L/2)‖·‖² at z
  have hsub : ∀ y, f z + L / 2 * ‖z‖ ^ 2 + inner ℝ G (y - z) ≤ f y + L / 2 * ‖y‖ ^ 2 := by
    intro y
    have h1 := hg y
    have hn := congrArg (fun t => L / 2 * t) (norm_sq_about' z y)
    rw [hG, inner_add_left, real_inner_smul_left]
    linarith
  have h1 := hsub y₁
  have h2 := hsub y₂
  -- the linear terms cancel
  have hsum : a • (y₁ - z) + b • (y₂ - z) = 0 := by
    have e : a • (y₁ - z) + b • (y₂ - z) = (a • y₁ + b • y₂) - (a + b) • z := by module
    rw [e, hab, one_smul, ← hz, sub_self]
  have hi : a * inner ℝ G (y₁ - z) + b * inner ℝ G (y₂ - z) = 0 := by
    rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right, hsum,
      inner_zero_right]
  have k1 := mul_le_mul_of_nonneg_left h1 ha
  have k2 := mul_le_mul_of_nonneg_left h2 hb
  have e : a * (f z + L / 2 * ‖z‖ ^ 2) + b * (f z + L / 2 * ‖z‖ ^ 2)
      = f z + L / 2 * ‖z‖ ^ 2 := by rw [← add_mul, hab, one_mul]
  nlinarith

/-- **`V - η V²` is semiconcave.** -/
theorem semiconcave_psi {V : EuclSpace d → ℝ} {lam η Cc : ℝ} (hlam : 0 ≤ lam) (hη : 0 ≤ η)
    (hV : SemiconvexWith lam (fun y => -V y))
    (hc : ∀ y, 0 ≤ 1 - 2 * η * V y) (hcC : ∀ y, 1 - 2 * η * V y ≤ Cc) :
    SemiconvexWith (Cc * lam) (fun y => -(V y - η * V y ^ 2)) := by
  apply semiconvex_of_supports
  intro x
  obtain ⟨P, hP⟩ := semiconvex_support hV x
  refine ⟨(1 - 2 * η * V x) • P, fun y => ?_⟩
  have h1 : -V x + inner ℝ P (y - x) - lam / 2 * ‖y - x‖ ^ 2 ≤ -V y := hP y
  have hc0 := hc x
  have hcx := hcC x
  -- ψ(V y) - ψ(V x) ≤ ψ'(V x)(V y - V x)
  have hψ : (V y - η * V y ^ 2) - (V x - η * V x ^ 2)
      = (1 - 2 * η * V x) * (V y - V x) - η * (V y - V x) ^ 2 := by ring
  have hsq : 0 ≤ η * (V y - V x) ^ 2 := by positivity
  have hcV : (1 - 2 * η * V x) * (V y - V x)
      ≤ (1 - 2 * η * V x) * (-inner ℝ P (y - x) + lam / 2 * ‖y - x‖ ^ 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hc0
  have hlamC : (1 - 2 * η * V x) * (lam / 2 * ‖y - x‖ ^ 2) ≤ Cc * (lam / 2 * ‖y - x‖ ^ 2) :=
    mul_le_mul_of_nonneg_right hcx (by positivity)
  rw [real_inner_smul_left]
  nlinarith

/-! ## Supersolution jets from superjets of `-V` -/

/-- The operator at `((-1) • q, (-1) • X)`. -/
theorem viscF_neg_one {p : ℝ} {q : EuclSpace d} (hq : q ≠ 0) (X : Bilin d) :
    viscF p ((-1 : ℝ) • q) ((-1 : ℝ) • X) = -viscF p q X := by
  have hqn : 0 < ‖q‖ := norm_pos_iff.2 hq
  rw [viscF_eq_neg, viscF_eq_neg]
  unfold normPLapOf infLaplacianOf
  rw [laplacianOf_smul]
  have hn : ‖(-1 : ℝ) • q‖ = ‖q‖ := by rw [norm_smul]; simp
  rw [hn]
  have e : ‖q‖⁻¹ • ((-1 : ℝ) • q) = (-1 : ℝ) • (‖q‖⁻¹ • q) := by rw [smul_comm]
  rw [e]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

/-- **A subjet of `V` gives a superjet of `-V`.** -/
theorem superJet_negOne_of_subJet {V : EuclSpace d → ℝ} {w q : EuclSpace d} {X : Bilin d}
    (h : (q, X) ∈ SubJet V w) :
    ((-1 : ℝ) • q, (-1 : ℝ) • X) ∈ SuperJet (fun y => -V y) w := by
  have h' : ∀ η > 0, ∀ᶠ y in 𝓝 w, V w + inner ℝ q (y - w)
      + 1 / 2 * (X (y - w)) (y - w) - η * ‖y - w‖ ^ 2 ≤ V y := h
  intro η hη
  filter_upwards [h' η hη] with y hy
  change -V y ≤ -V w + inner ℝ ((-1 : ℝ) • q) (y - w)
    + 1 / 2 * (((-1 : ℝ) • X) (y - w)) (y - w) + η * ‖y - w‖ ^ 2
  rw [real_inner_smul_left, smul_apply, smul_apply, smul_eq_mul]
  linarith

/-- **The supersolution jet inequality, from superjets of `-V`.** -/
theorem subJet_ineq_of_neg {p : ℝ} {O : Set (EuclSpace d)} {V : EuclSpace d → ℝ}
    (hneg : ∀ w ∈ O, ∀ (q : EuclSpace d) (X : Bilin d),
      (q, X) ∈ SuperJet (fun y => -V y) w → q ≠ 0 → viscF p q X ≤ 0) :
    ∀ w ∈ O, ∀ (q : EuclSpace d) (X : Bilin d), (q, X) ∈ SubJet V w →
      q ≠ 0 → 0 ≤ viscF p q X := by
  intro w hw q X hj hq
  have hq' : (-1 : ℝ) • q ≠ 0 := smul_ne_zero (by norm_num) hq
  have h1 := hneg w hw _ _ (superJet_negOne_of_subJet hj) hq'
  rw [viscF_neg_one hq] at h1
  linarith

end

end PLaplacian
