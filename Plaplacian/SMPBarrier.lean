/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.JensenProduct

@[expose] public section

/-! # The barrier for the strong maximum principle

The barrier is the quartic polynomial `φ(y) = (‖y - y₀‖² - B)²`. It is never
differentiated: at a maximum `w` of `u + ε φ`, its exact second-order
expansion turns the maximum into a superjet of `u` at `w`, and the jet bridge
`superJet_regular` applies to that.

With `v = w - y₀` and `s = ‖v‖²`,

  `φ(w + h) - φ(w) = 4(s - B)⟪v, h⟫ + 2(s - B)‖h‖² + 4⟪v, h⟫²
                     + 4⟪v, h⟫‖h‖² + ‖h‖⁴`,

so at a maximum of `u + ε φ` the pair `(c v, c I - 8ε v ⊗ v)`, `c = 4ε(B - s)`,
is a superjet of `u`, the cubic and quartic terms being absorbed into `η‖h‖²`.
On this pair the operator is computed from the two traces
`tr I = d`, `tr (v ⊗ v) = ‖v‖²`, and the value of the form at the unit vector
`v/‖v‖`.
-/

open Set Topology Filter Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-! ## The rank-one form and two traces -/

/-- **The rank-one form** `(u, w) ↦ ⟪v, u⟫ ⟪v, w⟫`. -/
def rankOne (v : EuclSpace d) : Bilin d :=
  (innerSL ℝ v).smulRight (innerSL ℝ v)

theorem rankOne_apply (v u w : EuclSpace d) :
    (rankOne v u) w = inner ℝ v u * inner ℝ v w := by
  simp [rankOne, smul_eq_mul]

theorem laplacianOf_add (X Y : Bilin d) :
    laplacianOf (X + Y) = laplacianOf X + laplacianOf Y := by
  simp [laplacianOf, Finset.sum_add_distrib]

theorem laplacianOf_sub (X Y : Bilin d) :
    laplacianOf (X - Y) = laplacianOf X - laplacianOf Y := by
  simp [laplacianOf, Finset.sum_sub_distrib]

theorem laplacianOf_idForm : laplacianOf (idForm d) = d := by
  unfold laplacianOf
  simp [idForm_apply]

theorem laplacianOf_rankOne (v : EuclSpace d) : laplacianOf (rankOne v) = ‖v‖ ^ 2 := by
  have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_inner_mul_inner v v
  simp only [EuclideanSpace.basisFun_apply] at h
  rw [real_inner_self_eq_norm_sq] at h
  unfold laplacianOf
  rw [← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [rankOne_apply, real_inner_comm (EuclideanSpace.single i (1 : ℝ)) v]

/-! ## The operator on the barrier's jet -/

/-- **The operator on `(c v, c I - b v ⊗ v)`**, for `c > 0` and `v ≠ 0`. -/
theorem viscF_barrierJet {p : ℝ} {v : EuclSpace d} (hv : v ≠ 0) {c b : ℝ} (hc : 0 < c) :
    viscF p (c • v) (c • idForm d - b • rankOne v)
      = -((c * d - b * ‖v‖ ^ 2) + (p - 2) * (c - b * ‖v‖ ^ 2)) := by
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  unfold viscF normPLapOf infLaplacianOf
  rw [laplacianOf_sub, laplacianOf_smul, laplacianOf_smul, laplacianOf_idForm,
    laplacianOf_rankOne]
  have hn : ‖c • v‖ = c * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have he : ‖c • v‖⁻¹ • (c • v) = ‖v‖⁻¹ • v := by
    rw [hn, smul_smul]
    congr 1
    field_simp
  rw [he]
  have h1 : ‖‖v‖⁻¹ • v‖ ^ 2 = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn.ne', one_pow]
  have h2 : inner ℝ v (‖v‖⁻¹ • v) = ‖v‖ := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  rw [sub_apply, sub_apply, smul_apply, smul_apply, smul_apply, smul_apply, smul_eq_mul,
    smul_eq_mul, idForm_apply, rankOne_apply, h1, h2]
  ring

/-! ## The barrier and its expansion -/

/-- **The barrier** `(‖y - y₀‖² - B)²`. -/
def barrier (y₀ : EuclSpace d) (B : ℝ) (y : EuclSpace d) : ℝ :=
  (‖y - y₀‖ ^ 2 - B) ^ 2

/-- **The exact expansion of the barrier.** -/
theorem barrier_expand (y₀ : EuclSpace d) (B : ℝ) (w h : EuclSpace d) :
    barrier y₀ B (w + h) - barrier y₀ B w
      = 4 * (‖w - y₀‖ ^ 2 - B) * inner ℝ (w - y₀) h + 2 * (‖w - y₀‖ ^ 2 - B) * ‖h‖ ^ 2
        + 4 * inner ℝ (w - y₀) h ^ 2 + 4 * inner ℝ (w - y₀) h * ‖h‖ ^ 2 + ‖h‖ ^ 4 := by
  unfold barrier
  have e : w + h - y₀ = (w - y₀) + h := by abel
  rw [e, norm_add_sq_real]
  ring

/-! ## The superjet at a maximum -/

/-- **A maximum of `u + ε φ` gives a superjet of `u`.** -/
theorem superJet_barrier {u : EuclSpace d → ℝ} {w y₀ : EuclSpace d} {B ε : ℝ}
    (hε : 0 < ε)
    (hloc : ∀ᶠ y in 𝓝 w, u y + ε * barrier y₀ B y ≤ u w + ε * barrier y₀ B w) :
    ((4 * ε * (B - ‖w - y₀‖ ^ 2)) • (w - y₀),
      (4 * ε * (B - ‖w - y₀‖ ^ 2)) • idForm d - (8 * ε) • rankOne (w - y₀))
      ∈ SuperJet u w := by
  intro η hη
  set v := w - y₀ with hv
  set s := ‖v‖ ^ 2 with hs
  set c := 4 * ε * (B - s) with hc
  have hρ : 0 < η / (ε * (4 * ‖v‖ + 1)) := by positivity
  filter_upwards [hloc, Metric.ball_mem_nhds w hρ] with y hy hyb
  rw [mem_ball, dist_eq_norm] at hyb
  set h := y - w with hhdef
  have hyw : y = w + h := by rw [hhdef]; abel
  have hexp := barrier_expand y₀ B w h
  rw [← hyw, ← hv, ← hs] at hexp
  -- the jet terms
  have hQ : inner ℝ (c • v) h = c * inner ℝ v h := real_inner_smul_left _ _ _
  have hX : ((c • idForm d - (8 * ε) • rankOne v) h) h
      = c * ‖h‖ ^ 2 - 8 * ε * (inner ℝ v h * inner ℝ v h) := by
    rw [sub_apply, sub_apply, smul_apply, smul_apply, smul_apply, smul_apply, smul_eq_mul,
      smul_eq_mul, idForm_apply, rankOne_apply]
  rw [hQ, hX]
  -- the remainder
  have hvh : |inner ℝ v h| ≤ ‖v‖ * ‖h‖ := abs_real_inner_le_norm v h
  have k1 : -(‖v‖ * ‖h‖) ≤ inner ℝ v h := neg_le_of_abs_le hvh
  have hh0 : 0 ≤ ‖h‖ := norm_nonneg h
  have hsmall : ε * (4 * ‖v‖ + 1) * ‖h‖ ≤ η := by
    have := (lt_div_iff₀ (by positivity : 0 < ε * (4 * ‖v‖ + 1))).1 hyb
    linarith
  have k2 : -(4 * ε * ‖v‖ * ‖h‖ ^ 3) ≤ 4 * ε * inner ℝ v h * ‖h‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right k1 (by positivity : (0 : ℝ) ≤ 4 * ε * ‖h‖ ^ 2)
    nlinarith
  have k3 : 4 * ε * ‖v‖ * ‖h‖ ^ 3 ≤ η * ‖h‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hsmall (by positivity : (0 : ℝ) ≤ ‖h‖ ^ 2)
    nlinarith [norm_nonneg v]
  have k4 : 0 ≤ ε * ‖h‖ ^ 4 := by positivity
  have hεexp := congrArg (fun t => ε * t) hexp
  rw [hc]
  nlinarith

end

end PLaplacian
