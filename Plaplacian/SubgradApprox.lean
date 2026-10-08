/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.GoodSet

/-! # Subgradients at a good point

Let `x = J(y)` with `J` the proximal map differentiable at `y`, `B = DJ(y)`
invertible, and `p₀ = y - x` a subgradient at `x`.

* **Uniqueness.** If `p` is a subgradient at `x`, so is every point of the
  segment from `p₀` to `p`; so `J(y + s v) = x` for `s ∈ [0, 1]`, `v = p - p₀`,
  and the derivative bound gives `s ‖B v‖ ≤ η s ‖v‖` for every `η > 0`. Hence
  `B v = 0` and `v = 0`.
* **Continuity.** Subgradients at points near `x` are near `p₀`: otherwise a
  bounded sequence of them, at points tending to `x`, would have a limit point
  that is a subgradient at `x` different from `p₀`.
* **Linear approximation.** For a subgradient `p` at `z`, put `w = z + p` and
  `h = w - y`; then `J(w) = z`, so `‖(z - x) - B h‖ ≤ η ‖h‖`, and inverting `B`
  gives `‖h‖ ≤ 2 ‖B⁻¹‖ ‖z - x‖` and
  `‖p - p₀ - (B⁻¹(z - x) - (z - x))‖ = ‖h - B⁻¹(z - x)‖ ≤ ε ‖z - x‖`.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



section prelim

/-- A convex combination of subgradients is a subgradient. -/
theorem isSubgrad_comb {f : EuclSpace d → ℝ} {x p q : EuclSpace d}
    (hp : IsSubgrad f x p) (hq : IsSubgrad f x q) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IsSubgrad f x ((1 - s) • p + s • q) := by
  intro w
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have h1 := mul_le_mul_of_nonneg_left (hp w) (by linarith : 0 ≤ 1 - s)
  have h2 := mul_le_mul_of_nonneg_left (hq w) hs0
  nlinarith

/-- **The derivative bound**, in the form used here. -/
theorem fderiv_approx {J : EuclSpace d → EuclSpace d} {B : EuclSpace d →L[ℝ] EuclSpace d}
    {y : EuclSpace d} (hJ : HasFDerivAt J B y) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ k : EuclSpace d, ‖k‖ < δ → ‖J (y + k) - J y - B k‖ ≤ η * ‖k‖ := by
  have h := (hasFDerivAt_iff_isLittleO_nhds_zero.1 hJ).def hη
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h
  exact ⟨δ, hδ, fun k hk => hball (by rwa [dist_zero_right])⟩

/-- **An invertible map has a continuous inverse.** -/
theorem exists_inv_of_det {B : EuclSpace d →L[ℝ] EuclSpace d} (hdet : B.det ≠ 0) :
    ∃ Binv : EuclSpace d →L[ℝ] EuclSpace d,
      (∀ v, Binv (B v) = v) ∧ (∀ v, B (Binv v) = v) := by
  have hu : IsUnit (B : EuclSpace d →ₗ[ℝ] EuclSpace d) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have hker := (LinearMap.isUnit_iff_ker_eq_bot _).1 hu
  have hran := (LinearMap.isUnit_iff_range_eq_top _).1 hu
  set Be := ContinuousLinearEquiv.ofBijective B hker hran with hBe
  have happ : ∀ v, Be v = B v := fun v => rfl
  refine ⟨(Be.symm : EuclSpace d →L[ℝ] EuclSpace d), fun v => ?_, fun v => ?_⟩
  · change Be.symm (B v) = v
    rw [← happ, ContinuousLinearEquiv.symm_apply_apply]
  · change B (Be.symm v) = v
    rw [← happ, ContinuousLinearEquiv.apply_symm_apply]

end prelim

section good

variable {f : EuclSpace d → ℝ} {x y : EuclSpace d}
  {B Binv : EuclSpace d →L[ℝ] EuclSpace d}

/-- **The subgradient at a good point is unique.** -/
theorem subgrad_unique_at_good (hf : ConvexOn ℝ univ f) (hJy : proxMap f y = x)
    (hd : HasFDerivAt (proxMap f) B y) (hinv : ∀ v, Binv (B v) = v)
    (hp0 : IsSubgrad f x (y - x)) {p : EuclSpace d} (hp : IsSubgrad f x p) :
    p = y - x := by
  set v := p - (y - x) with hv
  -- J is constant along the segment from y in the direction v
  have hconst : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → proxMap f (y + s • v) = x := by
    intro s hs0 hs1
    have hsub := isSubgrad_comb hp0 hp hs0 hs1
    have e : x + ((1 - s) • (y - x) + s • p) = y + s • v := by rw [hv]; module
    rw [← e]
    exact prox_of_subgrad hf hsub
  -- so B v = 0
  have hBv : B v = 0 := by
    by_contra hne
    have hpos : 0 < ‖B v‖ := norm_pos_iff.2 hne
    set η := ‖B v‖ / (2 * (‖v‖ + 1)) with hηdef
    have hη : 0 < η := by positivity
    obtain ⟨δ, hδ, hbd⟩ := fderiv_approx hd hη
    set s := min 1 (δ / (2 * (‖v‖ + 1))) with hsdef
    have hs0 : 0 < s := lt_min one_pos (by positivity)
    have hs1 : s ≤ 1 := min_le_left _ _
    have hsv : ‖s • v‖ < δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
      have : s ≤ δ / (2 * (‖v‖ + 1)) := min_le_right _ _
      have h2 : s * ‖v‖ ≤ δ / (2 * (‖v‖ + 1)) * ‖v‖ :=
        mul_le_mul_of_nonneg_right this (norm_nonneg v)
      have h3 : δ / (2 * (‖v‖ + 1)) * ‖v‖ < δ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [norm_nonneg v]
      linarith
    have h1 := hbd (s • v) hsv
    rw [hconst s hs0.le hs1, hJy, sub_self, zero_sub, norm_neg, map_smul, norm_smul,
      norm_smul, Real.norm_eq_abs, abs_of_pos hs0] at h1
    -- s ‖B v‖ ≤ η s ‖v‖, so ‖B v‖ ≤ η ‖v‖ < ‖B v‖
    have h2 : ‖B v‖ ≤ η * ‖v‖ := by
      have := le_of_mul_le_mul_left (by linarith : s * ‖B v‖ ≤ s * (η * ‖v‖)) hs0
      exact this
    have h3 : η * ‖v‖ < ‖B v‖ := by
      rw [hηdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg v]
    linarith
  have hv0 : v = 0 := by rw [← hinv v, hBv, map_zero]
  rw [hv] at hv0
  exact sub_eq_zero.1 hv0

/-- **Subgradients near a good point are near its subgradient.** -/
theorem subgrad_near_at_good (hf : ConvexOn ℝ univ f) (hJy : proxMap f y = x)
    (hd : HasFDerivAt (proxMap f) B y) (hinv : ∀ v, Binv (B v) = v)
    (hp0 : IsSubgrad f x (y - x)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z p : EuclSpace d, ‖z - x‖ < δ → IsSubgrad f z p → ‖p - (y - x)‖ < ε := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ z p : EuclSpace d, ‖z - x‖ < 1 / ((n : ℝ) + 1) ∧
      IsSubgrad f z p ∧ ε ≤ ‖p - (y - x)‖ := fun n => hcon _ (by positivity)
  choose zs ps hzs hps hpe using hseq
  obtain ⟨M, hM⟩ := convex_bdd_above_ball hf x (2 * 1)
  obtain ⟨m, hm⟩ := convex_bdd_below_ball hf x (2 * 1)
  have hzb : ∀ n, zs n ∈ closedBall x 1 := fun n => by
    rw [mem_closedBall, dist_eq_norm]
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; have := Nat.cast_nonneg (α := ℝ) n; linarith
    linarith [hzs n]
  have hpb : ∀ n, ‖ps n‖ ≤ M - m := fun n => by
    have := subgrad_norm_le one_pos hM hm (hzb n) (hps n)
    linarith
  have hzT : Tendsto zs atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hzs n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨q, _, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded (isBounded_closedBall (x := (0 : EuclSpace d)) (r := M - m))
      (fun n => mem_closedBall_zero_iff.2 (hpb n))
  have hq : IsSubgrad f x q := isSubgrad_of_tendsto (convex_continuous hf)
    (zs := fun n => zs (φ n)) (ps := fun n => ps (φ n)) (hzT.comp hφ.tendsto_atTop)
    hlim (fun n => hps _)
  have hqe := subgrad_unique_at_good hf hJy hd hinv hp0 hq
  have hlim' : Tendsto (fun n => ‖ps (φ n) - (y - x)‖) atTop (𝓝 0) := by
    have := (hlim.sub_const (y - x)).norm
    rwa [hqe, sub_self, norm_zero] at this
  have hge : ∀ n, ε ≤ ‖ps (φ n) - (y - x)‖ := fun n => hpe _
  have := ge_of_tendsto hlim' (Eventually.of_forall hge)
  linarith

/-- **The linear approximation of subgradients at a good point.** -/
theorem subgrad_linear_approx (hf : ConvexOn ℝ univ f) (hJy : proxMap f y = x)
    (hd : HasFDerivAt (proxMap f) B y) (hinv : ∀ v, Binv (B v) = v)
    (hp0 : IsSubgrad f x (y - x)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z p : EuclSpace d, ‖z - x‖ < δ → IsSubgrad f z p →
      ‖p - (y - x) - (Binv (z - x) - (z - x))‖ ≤ ε * ‖z - x‖ := by
  set Ci := ‖Binv‖ with hCi
  have hCi0 : 0 ≤ Ci := norm_nonneg _
  set η := min (1 / (2 * (Ci + 1))) (ε / (2 * (Ci + 1) ^ 2)) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hη1 : η ≤ 1 / (2 * (Ci + 1)) := min_le_left _ _
  have hη2 : η ≤ ε / (2 * (Ci + 1) ^ 2) := min_le_right _ _
  obtain ⟨δ₁, hδ₁, hbd⟩ := fderiv_approx hd hη
  obtain ⟨δ₂, hδ₂, hnear⟩ :=
    subgrad_near_at_good hf hJy hd hinv hp0 (by linarith : 0 < δ₁ / 2)
  refine ⟨min δ₂ (δ₁ / 2), lt_min hδ₂ (by linarith), fun z p hz hp => ?_⟩
  have hz2 : ‖z - x‖ < δ₂ := lt_of_lt_of_le hz (min_le_left _ _)
  have hz1 : ‖z - x‖ < δ₁ / 2 := lt_of_lt_of_le hz (min_le_right _ _)
  set h := (z - x) + (p - (y - x)) with hhdef
  have hh : ‖h‖ < δ₁ := by
    have := hnear z p hz2 hp
    calc ‖h‖ ≤ ‖z - x‖ + ‖p - (y - x)‖ := norm_add_le _ _
      _ < δ₁ / 2 + δ₁ / 2 := by linarith
      _ = δ₁ := by ring
  -- J(y + h) = z
  have hw : y + h = z + p := by rw [hhdef]; abel
  have hJw : proxMap f (y + h) = z := by rw [hw]; exact prox_of_subgrad hf hp
  have h1 := hbd h hh
  rw [hJw, hJy] at h1
  -- ‖h‖ ≤ 2 Ci ‖z - x‖
  have hinvb : ‖h‖ ≤ Ci * ‖B h‖ := by
    calc ‖h‖ = ‖Binv (B h)‖ := by rw [hinv h]
      _ ≤ Ci * ‖B h‖ := ContinuousLinearMap.le_opNorm _ _
  have hBh : ‖B h‖ ≤ ‖z - x‖ + η * ‖h‖ := by
    have e : B h = (z - x) - (z - x - B h) := by abel
    rw [e]
    calc ‖(z - x) - (z - x - B h)‖ ≤ ‖z - x‖ + ‖z - x - B h‖ := norm_sub_le _ _
      _ ≤ ‖z - x‖ + η * ‖h‖ := by linarith
  have hCη : Ci * η ≤ 1 / 2 := by
    have : Ci * η ≤ Ci * (1 / (2 * (Ci + 1))) := mul_le_mul_of_nonneg_left hη1 hCi0
    have e : Ci * (1 / (2 * (Ci + 1))) ≤ 1 / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hh2 : ‖h‖ ≤ 2 * Ci * ‖z - x‖ := by
    have hnh : 0 ≤ ‖h‖ := norm_nonneg _
    have h3 := mul_le_mul_of_nonneg_left hBh hCi0
    nlinarith
  -- the approximation
  have e2 : p - (y - x) - (Binv (z - x) - (z - x)) = Binv (B h - (z - x)) := by
    rw [map_sub Binv (B h) (z - x), hinv h, hhdef]; abel
  rw [e2]
  have h4 : ‖Binv (B h - (z - x))‖ ≤ Ci * (η * ‖h‖) := by
    calc ‖Binv (B h - (z - x))‖ ≤ Ci * ‖B h - (z - x)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Ci * (η * ‖h‖) := by
          apply mul_le_mul_of_nonneg_left _ hCi0
          rw [norm_sub_rev]; exact h1
  have h5 : Ci * (η * ‖h‖) ≤ Ci * η * (2 * Ci * ‖z - x‖) := by
    have := mul_le_mul_of_nonneg_left hh2 (mul_nonneg hCi0 hη.le)
    nlinarith
  have h6 : Ci * η * (2 * Ci) ≤ ε := by
    have : 2 * Ci ^ 2 * η ≤ 2 * Ci ^ 2 * (ε / (2 * (Ci + 1) ^ 2)) :=
      mul_le_mul_of_nonneg_left hη2 (by positivity)
    have e : 2 * Ci ^ 2 * (ε / (2 * (Ci + 1) ^ 2)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg Ci]
    nlinarith
  have h7 : Ci * η * (2 * Ci * ‖z - x‖) ≤ ε * ‖z - x‖ := by
    have := mul_le_mul_of_nonneg_right h6 (norm_nonneg (z - x))
    nlinarith
  linarith

end good

end

end PLaplacian
