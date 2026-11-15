/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Reduce2

@[expose] public section

/-! # Transferring jets back to the original functions

The core produces jets of the convolutions; the magic property turns them into
jets of `ũ` and `ṽ` at the maximizers; this file turns those into jets of `u`
and `v`. Since

  `u(y) = ũ(y - x̂) + K ‖y - x̂‖⁴ + ⟪q, y⟫ + c_u`,
  `v(y) = ṽ(y - ŷ) - K ‖y - ŷ‖⁴ + ⟪q, y⟫ + c_v`,

a jet of `ũ` at `x` gives one of `u` at `x̂ + x`, with the quartic's jet, scaled
by `K`, and the gradient `q` added. Also here: scaling jets by a nonnegative
constant, and the continuity of semiconvex functions, which makes the values of
the convolutions converge.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



section scale

variable {f : EuclSpace d → ℝ} {x q : EuclSpace d} {X : Bilin d} {c : ℝ}

/-- **Scaling a superjet** by a nonnegative constant. -/
theorem superJet_smul (hc : 0 ≤ c) (h : (q, X) ∈ SuperJet f x) :
    (c • q, c • X) ∈ SuperJet (fun y => c * f y) x := by
  intro η hη
  have hη' : 0 < η / (c + 1) := by positivity
  filter_upwards [h (η / (c + 1)) hη'] with y hy
  change f y ≤ f x + inner ℝ q (y - x) + (1 / 2) * (X (y - x)) (y - x)
    + η / (c + 1) * ‖y - x‖ ^ 2 at hy
  change c * f y ≤ c * f x + inner ℝ (c • q) (y - x)
    + (1 / 2) * ((c • X) (y - x)) (y - x) + η * ‖y - x‖ ^ 2
  rw [real_inner_smul_left, smul_form_apply]
  have h1 := mul_le_mul_of_nonneg_left hy hc
  have h2 : c * (η / (c + 1)) ≤ η := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  have h3 : c * (η / (c + 1)) * ‖y - x‖ ^ 2 ≤ η * ‖y - x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  nlinarith

/-- **Scaling a subjet** by a nonnegative constant. -/
theorem subJet_smul (hc : 0 ≤ c) (h : (q, X) ∈ SubJet f x) :
    (c • q, c • X) ∈ SubJet (fun y => c * f y) x := by
  intro η hη
  have hη' : 0 < η / (c + 1) := by positivity
  filter_upwards [h (η / (c + 1)) hη'] with y hy
  change f x + inner ℝ q (y - x) + (1 / 2) * (X (y - x)) (y - x)
    - η / (c + 1) * ‖y - x‖ ^ 2 ≤ f y at hy
  change c * f x + inner ℝ (c • q) (y - x)
    + (1 / 2) * ((c • X) (y - x)) (y - x) - η * ‖y - x‖ ^ 2 ≤ c * f y
  rw [real_inner_smul_left, smul_form_apply]
  have h1 := mul_le_mul_of_nonneg_left hy hc
  have h2 : c * (η / (c + 1)) ≤ η := by
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
  have h3 : c * (η / (c + 1)) * ‖y - x‖ ^ 2 ≤ η * ‖y - x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  nlinarith

end scale

/-- **A semiconvex function is continuous.** -/
theorem semiconvex_continuous {lam : ℝ} {f : EuclSpace d → ℝ}
    (hf : SemiconvexWith lam f) : Continuous f := by
  have hc : ContinuousOn (fun x => f x + lam / 2 * ‖x‖ ^ 2) univ :=
    ConvexOn.continuousOn isOpen_univ hf
  have hc' : Continuous (fun x => f x + lam / 2 * ‖x‖ ^ 2) :=
    continuousOn_univ.1 hc
  have hq : Continuous (fun x : EuclSpace d => lam / 2 * ‖x‖ ^ 2) := by fun_prop
  have heq : f = fun x => (f x + lam / 2 * ‖x‖ ^ 2) - lam / 2 * ‖x‖ ^ 2 := by
    funext x; ring
  rw [heq]
  exact hc'.sub hq

section transfer

variable {u v : EuclSpace d → ℝ} {q xh yh x y a b : EuclSpace d} {X Y : Bilin d}
  {K : ℝ}

/-- `u` in terms of `ũ`. -/
theorem u_eq_uTilde (u : EuclSpace d → ℝ) (q xh : EuclSpace d) (K : ℝ) :
    u = fun z => uTilde u q xh K (z + -xh) + K * ‖z - xh‖ ^ 4 + inner ℝ q z
      + (u xh - inner ℝ q xh) := by
  funext z
  unfold uTilde
  have e1 : xh + (z + -xh) = z := by abel
  have e2 : z + -xh = z - xh := (sub_eq_add_neg z xh).symm
  rw [e1, e2]
  ring

/-- `v` in terms of `ṽ`. -/
theorem v_eq_vTilde (v : EuclSpace d → ℝ) (q yh : EuclSpace d) (K : ℝ) :
    v = fun z => vTilde v q yh K (z + -yh) + -K * ‖z - yh‖ ^ 4 + inner ℝ q z
      + (v yh - inner ℝ q yh) := by
  funext z
  unfold vTilde
  have e1 : yh + (z + -yh) = z := by abel
  have e2 : z + -yh = z - yh := (sub_eq_add_neg z yh).symm
  rw [e1, e2]
  ring

/-- **The transfer of a superjet from `ũ` to `u`.** -/
theorem superJet_u_of_uTilde (hK : 0 ≤ K) (h : (a, X) ∈ SuperJet (uTilde u q xh K) x) :
    (a + K • ((4 * ‖x‖ ^ 2) • x) + q, X + K • ((12 * ‖x‖ ^ 2) • idForm d))
      ∈ SuperJet u (xh + x) := by
  have h1 : (a, X) ∈ SuperJet (fun z => uTilde u q xh K (z + -xh)) (xh + x) := by
    apply superJet_comp_add
    have e : xh + x + -xh = x := by abel
    rw [e]; exact h
  have h2 := superJet_quartic xh (xh + x)
  have e : xh + x - xh = x := by abel
  rw [e] at h2
  have h3 := superJet_smul hK h2
  have h4 := superJet_add h1 h3
  have h5 := superJet_add_affine h4 q (u xh - inner ℝ q xh)
  exact superJet_congr (u_eq_uTilde u q xh K).symm h5

/-- **The transfer of a subjet from `ṽ` to `v`.** -/
theorem subJet_v_of_vTilde (hK : 0 ≤ K) (h : (b, Y) ∈ SubJet (vTilde v q yh K) y) :
    (b + K • (-((4 * ‖y‖ ^ 2) • y)) + q, Y + K • (-((12 * ‖y‖ ^ 2) • idForm d)))
      ∈ SubJet v (yh + y) := by
  have h1 : (b, Y) ∈ SubJet (fun z => vTilde v q yh K (z + -yh)) (yh + y) := by
    apply subJet_comp_add
    have e : yh + y + -yh = y := by abel
    rw [e]; exact h
  have h2 := subJet_neg_quartic yh (yh + y)
  have e : yh + y - yh = y := by abel
  rw [e] at h2
  have h3 := subJet_smul hK h2
  have h4 := subJet_add h1 h3
  have h5 := subJet_add_affine h4 q (v yh - inner ℝ q yh)
  have hfun : (fun z => vTilde v q yh K (z + -yh) + K * -‖z - yh‖ ^ 4
        + inner ℝ q z + (v yh - inner ℝ q yh)) = v := by
    funext z
    unfold vTilde
    have e1 : yh + (z + -yh) = z := by abel
    have e2 : z + -yh = z - yh := (sub_eq_add_neg z yh).symm
    rw [e1, e2]
    ring
  exact subJet_congr hfun h5

/-- The value of `u` in terms of `ũ`. -/
theorem u_apply_eq (u : EuclSpace d → ℝ) (q xh : EuclSpace d) (K : ℝ)
    (x : EuclSpace d) :
    u (xh + x) = uTilde u q xh K x + inner ℝ q (xh + x) + K * ‖x‖ ^ 4
      + (u xh - inner ℝ q xh) := by
  unfold uTilde; ring

/-- The value of `v` in terms of `ṽ`. -/
theorem v_apply_eq (v : EuclSpace d → ℝ) (q yh : EuclSpace d) (K : ℝ)
    (y : EuclSpace d) :
    v (yh + y) = vTilde v q yh K y + inner ℝ q (yh + y) - K * ‖y‖ ^ 4
      + (v yh - inner ℝ q yh) := by
  unfold vTilde; ring

end transfer

end

end PLaplacian
