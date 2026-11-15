/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.DiscComp

@[expose] public section

/-! # The boundary barrier

With `s = |x - z|²` and `t = s - δ²`, the barrier is `ψ = t - M t²`.

* It is a polynomial in `x`, so smooth.
* At `w`, with `v = w - z` and `c = 2(1 - 2Mt)`, it has the exact expansion
  `(c v, c I - 8M v ⊗ v)`, with remainder `-4M⟪v, h⟫|h|² - M|h|⁴`.
* On the shell `δ² ≤ s ≤ δ² + 1/(4M)`, `1 ≤ c ≤ 2`, so the gradient is nonzero and
  `Δᴺₚψ = c(d + p - 2) - 8M(p - 1)s ≤ 2(d + p - 2) - 8M(p - 1)δ²`, which is `-1` for
  `M = (2(d + p - 2) + 1)/(8(p - 1)δ²)`.
* `ψ ≥ (3/4) t ≥ 0` there, with `ψ = 0` on the sphere `s = δ²`.

Through `normPLapOf_of_peano`, the operator value at `(∇ψ, D²ψ)` is read off the
explicit expansion.
-/

open Set Topology Filter Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- **The barrier.** -/
def bpsi (z : EuclSpace d) (δ M : ℝ) (x : EuclSpace d) : ℝ :=
  (‖x - z‖ ^ 2 - δ ^ 2) - M * (‖x - z‖ ^ 2 - δ ^ 2) ^ 2

/-- The constant `M`. -/
def bM (p δ : ℝ) (d : ℕ) : ℝ := (2 * ((d : ℝ) + p - 2) + 1) / (8 * (p - 1) * δ ^ 2)

theorem bpsi_contDiff (z : EuclSpace d) (δ M : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (bpsi z δ M) := by
  have hs : ContDiff ℝ n (fun x : EuclSpace d => ‖x - z‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  unfold bpsi
  exact (hs.sub contDiff_const).sub (contDiff_const.mul ((hs.sub contDiff_const).pow 2))

/-- **The exact expansion of the barrier.** -/
theorem bpsi_expand (z : EuclSpace d) (δ M : ℝ) (w h : EuclSpace d) :
    bpsi z δ M (w + h) - bpsi z δ M w
      = 2 * (1 - 2 * M * (‖w - z‖ ^ 2 - δ ^ 2)) * inner ℝ (w - z) h
        + ((1 - 2 * M * (‖w - z‖ ^ 2 - δ ^ 2)) * ‖h‖ ^ 2 - 4 * M * inner ℝ (w - z) h ^ 2)
        + (-4 * M * inner ℝ (w - z) h * ‖h‖ ^ 2 - M * ‖h‖ ^ 4) := by
  unfold bpsi
  have e : w + h - z = (w - z) + h := by abel
  rw [e, norm_add_sq_real]
  ring

/-- **The Peano expansion of the barrier.** -/
theorem bpsi_peano {M : ℝ} (hM : 0 ≤ M) (z : EuclSpace d) (δ : ℝ) (w : EuclSpace d) :
    PeanoAt (bpsi z δ M) w ((2 * (1 - 2 * M * (‖w - z‖ ^ 2 - δ ^ 2))) • (w - z))
      ((2 * (1 - 2 * M * (‖w - z‖ ^ 2 - δ ^ 2))) • idForm d - (8 * M) • rankOne (w - z)) := by
  intro ε hε
  set v := w - z with hv
  set c := 2 * (1 - 2 * M * (‖v‖ ^ 2 - δ ^ 2)) with hc
  set ρ := min 1 (ε / (4 * M * ‖v‖ + M + 1)) with hρ
  have hρ0 : 0 < ρ := lt_min one_pos (by positivity)
  refine ⟨ρ, hρ0, fun k hk => ?_⟩
  have hk1 : ‖k‖ ≤ 1 := le_trans hk.le (min_le_left _ _)
  have hk2 : ‖k‖ ≤ ε / (4 * M * ‖v‖ + M + 1) := le_trans hk.le (min_le_right _ _)
  have hexp := bpsi_expand z δ M w k
  rw [← hv] at hexp
  have hQ : inner ℝ (c • v) k = c * inner ℝ v k := real_inner_smul_left _ _ _
  have hX : ((c • idForm d - (8 * M) • rankOne v) k) k
      = c * ‖k‖ ^ 2 - 8 * M * (inner ℝ v k * inner ℝ v k) := by
    simp only [sub_apply, smul_apply, smul_eq_mul, idForm_apply, rankOne_apply]
  rw [hQ, hX]
  have key : bpsi z δ M (w + k) - bpsi z δ M w - c * inner ℝ v k
      - 1 / 2 * (c * ‖k‖ ^ 2 - 8 * M * (inner ℝ v k * inner ℝ v k))
      = -4 * M * inner ℝ v k * ‖k‖ ^ 2 - M * ‖k‖ ^ 4 := by
    rw [hexp, hc]; ring
  rw [key]
  -- the remainder
  have hvk : |inner ℝ v k| ≤ ‖v‖ * ‖k‖ := abs_real_inner_le_norm v k
  have hk0 : 0 ≤ ‖k‖ := norm_nonneg k
  have hk4 : ‖k‖ ^ 4 ≤ ‖k‖ ^ 3 := by
    have : ‖k‖ ^ 4 = ‖k‖ ^ 3 * ‖k‖ := by ring
    rw [this]
    calc ‖k‖ ^ 3 * ‖k‖ ≤ ‖k‖ ^ 3 * 1 := mul_le_mul_of_nonneg_left hk1 (by positivity)
      _ = ‖k‖ ^ 3 := mul_one _
  have hrem : |-4 * M * inner ℝ v k * ‖k‖ ^ 2 - M * ‖k‖ ^ 4|
      ≤ (4 * M * ‖v‖ + M) * ‖k‖ ^ 3 := by
    obtain ⟨a1, a2⟩ := abs_le.1 hvk
    have b1 : -(4 * M * (‖v‖ * ‖k‖) * ‖k‖ ^ 2) ≤ 4 * M * inner ℝ v k * ‖k‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right a1 (by positivity : (0 : ℝ) ≤ 4 * M * ‖k‖ ^ 2)
      nlinarith
    have b2 : 4 * M * inner ℝ v k * ‖k‖ ^ 2 ≤ 4 * M * (‖v‖ * ‖k‖) * ‖k‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right a2 (by positivity : (0 : ℝ) ≤ 4 * M * ‖k‖ ^ 2)
      nlinarith
    have b3 : 0 ≤ M * ‖k‖ ^ 4 := by positivity
    have b4 : M * ‖k‖ ^ 4 ≤ M * ‖k‖ ^ 3 := mul_le_mul_of_nonneg_left hk4 hM
    rw [abs_le]
    constructor <;> nlinarith
  have hfin : (4 * M * ‖v‖ + M) * ‖k‖ ^ 3 ≤ ε * ‖k‖ ^ 2 := by
    have h1 : (4 * M * ‖v‖ + M + 1) * ‖k‖ ≤ ε := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * M * ‖v‖ + M + 1)).1 hk2
      linarith
    have h2 : (4 * M * ‖v‖ + M) * ‖k‖ ≤ ε := by nlinarith [norm_nonneg v]
    have := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ ‖k‖ ^ 2)
    nlinarith
  linarith

/-- The operator at `(v, I)`. -/
theorem normPLapOf_idForm {p : ℝ} {v : EuclSpace d} (hv : v ≠ 0) :
    normPLapOf p v (idForm d) = (d : ℝ) + p - 2 := by
  have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
  unfold normPLapOf infLaplacianOf
  rw [laplacianOf_idForm, idForm_apply, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ hvn.ne', one_pow]
  ring

/-- **On the shell, the barrier has nonzero gradient and `Δᴺₚψ ≤ -1`.** -/
theorem bpsi_op (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p) {δ : ℝ} (hδ : 0 < δ) (z : EuclSpace d)
    {w : EuclSpace d} (h1 : δ ^ 2 ≤ ‖w - z‖ ^ 2)
    (h2 : ‖w - z‖ ^ 2 ≤ δ ^ 2 + 1 / (4 * bM p δ d)) :
    gradient (bpsi z δ (bM p δ d)) w ≠ 0 ∧
      normPLapOf p (gradient (bpsi z δ (bM p δ d)) w) (hess (bpsi z δ (bM p δ d)) w)
        ≤ -1 := by
  have hp1 : 0 < p - 1 := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hD : 0 < (d : ℝ) + p - 2 := by linarith
  set M := bM p δ d with hMdef
  have hM : 0 < M := by rw [hMdef]; unfold bM; positivity
  set v := w - z with hv
  set t := ‖v‖ ^ 2 - δ ^ 2 with ht
  have ht0 : 0 ≤ t := by linarith
  have hMt : M * t ≤ 1 / 4 := by
    have : t ≤ 1 / (4 * M) := by linarith
    have h := mul_le_mul_of_nonneg_left this hM.le
    have e : M * (1 / (4 * M)) = 1 / 4 := by field_simp
    linarith
  set c := 2 * (1 - 2 * M * t) with hc
  have hc1 : 1 ≤ c := by rw [hc]; nlinarith
  have hc2 : c ≤ 2 := by rw [hc]; nlinarith [mul_nonneg hM.le ht0]
  have hv0 : v ≠ 0 := by
    intro h
    rw [h, norm_zero] at ht
    have : t = -δ ^ 2 := by rw [ht]; ring
    nlinarith [pow_pos hδ 2]
  -- the operator value, from the explicit expansion
  obtain ⟨hgrad, hval⟩ := normPLapOf_of_peano (p := p) (bpsi_contDiff z δ M)
    (bpsi_peano hM.le z δ w)
  rw [← hv, ← ht, ← hc] at hgrad hval
  have hcpos : 0 < c := by linarith
  refine ⟨?_, ?_⟩
  · rw [hgrad]; exact smul_ne_zero hcpos.ne' hv0
  · rw [hval, normPLapOf_cv_sub hv0 hcpos, normPLapOf_idForm hv0]
    -- c(d + p - 2) - 8M(p - 1)‖v‖² ≤ 2(d + p - 2) - 8M(p - 1)δ² = -1
    have hMδ : 8 * M * (p - 1) * δ ^ 2 = 2 * ((d : ℝ) + p - 2) + 1 := by
      rw [hMdef]; unfold bM; field_simp
    have k1 : c * ((d : ℝ) + p - 2) ≤ 2 * ((d : ℝ) + p - 2) :=
      mul_le_mul_of_nonneg_right hc2 hD.le
    have k2 : 8 * M * (p - 1) * δ ^ 2 ≤ (p - 1) * (8 * M) * ‖v‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 8 * M * (p - 1))
      nlinarith
    linarith

/-- **The barrier is nonnegative on the shell.** -/
theorem bpsi_nonneg {M δ : ℝ} (hM : 0 < M) (z : EuclSpace d) {w : EuclSpace d}
    (h1 : δ ^ 2 ≤ ‖w - z‖ ^ 2) (h2 : ‖w - z‖ ^ 2 ≤ δ ^ 2 + 1 / (4 * M)) :
    3 / 4 * (‖w - z‖ ^ 2 - δ ^ 2) ≤ bpsi z δ M w := by
  unfold bpsi
  set t := ‖w - z‖ ^ 2 - δ ^ 2 with ht
  have ht0 : 0 ≤ t := by linarith
  have hMt : M * t ≤ 1 / 4 := by
    have : t ≤ 1 / (4 * M) := by linarith
    have h := mul_le_mul_of_nonneg_left this hM.le
    have e : M * (1 / (4 * M)) = 1 / 4 := by field_simp
    linarith
  nlinarith

end

end PLaplacian
