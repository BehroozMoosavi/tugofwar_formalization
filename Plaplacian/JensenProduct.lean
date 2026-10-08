/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.JensenEucl

/-! # Jensen's lemma on the product, and the comparison principle

`JensenLemma d` is stated on `E × E`, where the doubled function lives, and is
derived here from `jensen_positive_measure` on `ℝ^{d+d}` through the continuous
linear equivalence `Φ = EuclideanSpace.finAddEquivProd`.

1. `‖v‖² = ‖(Φ v).1‖² + ‖(Φ v).2‖²`, and by polarization the inner product
   splits likewise; so the Euclidean norm dominates the maximum norm of the
   product.
2. `W = w ∘ Φ` is semiconvex with constant `C = max λ 0`.
3. The strict maximum of `w` on the product ball gives a strict maximum of `W`
   on the Euclidean ball, and compactness of the sphere a gap `γ`; with
   `δ' = min δ (γ/4r)` the hypothesis on the sphere holds.
4. `Φ` maps the Euclidean Jensen set into the product one, and positive measure
   transfers through `null_image_cle`.

With `JensenLemma d` proved, the comparison principle for strict subsolutions
holds with no hypothesis beyond its statement.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- The Euclidean identification of `ℝ^{d+d}` with the product. -/
abbrev Φsplit (d : ℕ) : EuclideanSpace ℝ (Fin (d + d)) ≃L[ℝ] EuclSpace d × EuclSpace d :=
  EuclideanSpace.finAddEquivProd

theorem Φsplit_norm_sq (v : EuclideanSpace ℝ (Fin (d + d))) :
    ‖v‖ ^ 2 = ‖(Φsplit d v).1‖ ^ 2 + ‖(Φsplit d v).2‖ ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_add]

theorem Φsplit_inner (u v : EuclideanSpace ℝ (Fin (d + d))) :
    inner ℝ u v = inner ℝ (Φsplit d u).1 (Φsplit d v).1
      + inner ℝ (Φsplit d u).2 (Φsplit d v).2 := by
  have h1 := Φsplit_norm_sq (u + v)
  have h2 := Φsplit_norm_sq u
  have h3 := Φsplit_norm_sq v
  rw [map_add, Prod.fst_add, Prod.snd_add, norm_add_sq_real, norm_add_sq_real,
    norm_add_sq_real] at h1
  linarith

theorem Φsplit_fst_le (v : EuclideanSpace ℝ (Fin (d + d))) : ‖(Φsplit d v).1‖ ≤ ‖v‖ := by
  have h := Φsplit_norm_sq v
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by nlinarith [sq_nonneg ‖(Φsplit d v).2‖])

theorem Φsplit_snd_le (v : EuclideanSpace ℝ (Fin (d + d))) : ‖(Φsplit d v).2‖ ≤ ‖v‖ := by
  have h := Φsplit_norm_sq v
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by nlinarith [sq_nonneg ‖(Φsplit d v).1‖])

theorem Φsplit_norm_le (v : EuclideanSpace ℝ (Fin (d + d))) : ‖Φsplit d v‖ ≤ ‖v‖ :=
  norm_prod_le_iff.2 ⟨Φsplit_fst_le v, Φsplit_snd_le v⟩

/-- **Jensen's lemma on the product.** -/
theorem jensen : JensenLemma d := by
  intro w lam hconv zh r hr hstrict δ hδ
  have hH : (volume : Measure (EuclSpace d × EuclSpace d)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  set Φ := Φsplit d with hΦdef
  set C := max lam 0 with hCdef
  have hC0 : 0 ≤ C := le_max_right _ _
  have hCl : 0 ≤ C - lam := sub_nonneg.2 (le_max_left _ _)
  set vh := Φ.symm zh with hvh
  have hΦvh : Φ vh = zh := Φ.apply_symm_apply zh
  set W : EuclideanSpace ℝ (Fin (d + d)) → ℝ := fun v => w (Φ v) with hWdef
  -- semiconvexity of W
  have hconvW : ConvexOn ℝ univ (fun v => W v + C / 2 * ‖v‖ ^ 2) := by
    refine ⟨convex_univ, fun a _ b _ s t hs ht hst => ?_⟩
    have h1 := hconv.2 (mem_univ (Φ a)) (mem_univ (Φ b)) hs ht hst
    simp only [smul_eq_mul] at h1 ⊢
    have hΦ : Φ (s • a + t • b) = s • Φ a + t • Φ b := by
      rw [map_add, map_smul, map_smul]
    have hn1 := Φsplit_norm_sq (s • a + t • b)
    have hna := Φsplit_norm_sq a
    have hnb := Φsplit_norm_sq b
    rw [← hΦdef, hΦ] at hn1
    rw [← hΦdef] at hna hnb
    rw [← hn1, ← hna, ← hnb] at h1
    have hsq := norm_sq_convex_comb hst a b
    have hab : 0 ≤ s * t * ‖a - b‖ ^ 2 := by positivity
    have hconvsq : ‖s • a + t • b‖ ^ 2 ≤ s * ‖a‖ ^ 2 + t * ‖b‖ ^ 2 := by linarith
    have h2 := mul_le_mul_of_nonneg_left hconvsq hCl
    simp only [hWdef]
    rw [hΦ]
    nlinarith
  have hWc : Continuous W := by
    have h1 := convex_continuous hconvW
    have h2 : Continuous (fun v : EuclideanSpace ℝ (Fin (d + d)) => C / 2 * ‖v‖ ^ 2) := by
      fun_prop
    convert h1.sub h2 using 1
    funext v
    simp
  -- the strict maximum on the Euclidean ball
  have hstrE : ∀ v ∈ closedBall vh r, v ≠ vh → W v < W vh := by
    intro v hv hne
    have hz : Φ v ∈ closedBall zh r := by
      rw [mem_closedBall, dist_eq_norm, ← hΦvh, ← map_sub]
      rw [mem_closedBall, dist_eq_norm] at hv
      exact (Φsplit_norm_le _).trans hv
    have hne' : Φ v ≠ zh := by
      intro h; apply hne
      rw [← hΦvh] at h
      exact Φ.injective h
    have := hstrict (Φ v) hz hne'
    simp only [hWdef, hΦvh]
    exact this
  -- the gap on the sphere
  obtain ⟨γ, hγ, hgap⟩ : ∃ γ > 0, ∀ y ∈ sphere vh r, W y ≤ W vh - γ := by
    by_cases hS : (sphere vh r).Nonempty
    · obtain ⟨y₀, hy₀, hmax⟩ := (isCompact_sphere vh r).exists_isMaxOn hS hWc.continuousOn
      have hy₀b : y₀ ∈ closedBall vh r := sphere_subset_closedBall hy₀
      have hy₀ne : y₀ ≠ vh := by
        intro h
        rw [h, mem_sphere, dist_self] at hy₀
        linarith
      have hlt := hstrE y₀ hy₀b hy₀ne
      exact ⟨W vh - W y₀, by linarith, fun y hy => by have h' : W y ≤ W y₀ := hmax hy; linarith⟩
    · refine ⟨1, one_pos, fun y hy => ?_⟩
      exact absurd ⟨y, hy⟩ hS
  set δ' := min δ (γ / (4 * r)) with hδ'def
  have hδ' : 0 < δ' := lt_min hδ (by positivity)
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  have hsphere : ∀ y, ‖y - vh‖ = r → W y + 2 * δ' * r < W vh := by
    intro y hy
    have h1 := hgap y (by rw [mem_sphere, dist_eq_norm]; exact hy)
    have h2 : δ' ≤ γ / (4 * r) := min_le_right _ _
    have h3 : 2 * δ' * r ≤ γ / 2 := by
      have := mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ 2 * r)
      have e : γ / (4 * r) * (2 * r) = γ / 2 := by field_simp; ring
      nlinarith
    linarith
  -- Jensen's lemma on ℝ^{d+d}
  have hpos := jensen_positive_measure W C hC0 hconvW vh vh r δ' hr hδ'
    (mem_closedBall_self hr.le) hsphere
  set KE := {x | x ∈ ball vh r ∧ ∃ p : EuclSpace (d + d), ‖p‖ ≤ δ' ∧
      ∀ y ∈ closedBall vh r, W y + inner ℝ p y ≤ W x + inner ℝ p x} with hKE
  -- Φ maps it into the product Jensen set
  have hsub : Φ '' KE ⊆ {z ∈ ball zh r | ∃ p₁ p₂ : EuclSpace d, ‖p₁‖ ≤ δ ∧ ‖p₂‖ ≤ δ ∧
      IsLocalMax (fun z' => w z' + inner ℝ p₁ z'.1 + inner ℝ p₂ z'.2) z} := by
    rintro _ ⟨v, ⟨hvb, p, hp, hmaxv⟩, rfl⟩
    refine ⟨?_, (Φ p).1, (Φ p).2, ?_, ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, ← hΦvh, ← map_sub]
      rw [mem_ball, dist_eq_norm] at hvb
      exact lt_of_le_of_lt (Φsplit_norm_le _) hvb
    · exact ((Φsplit_fst_le p).trans hp).trans hδ'δ
    · exact ((Φsplit_snd_le p).trans hp).trans hδ'δ
    · unfold IsLocalMax IsMaxFilter
      have hnb : Φ.symm ⁻¹' (ball vh r) ∈ 𝓝 (Φ v) := by
        apply Φ.symm.continuous.continuousAt.preimage_mem_nhds
        rw [Φ.symm_apply_apply]
        exact isOpen_ball.mem_nhds hvb
      filter_upwards [hnb] with z' hz'
      have hz'b : Φ.symm z' ∈ closedBall vh r := ball_subset_closedBall hz'
      have h1 := hmaxv (Φ.symm z') hz'b
      simp only [hWdef, Φ.apply_symm_apply] at h1
      rw [Φsplit_inner p (Φ.symm z'), Φsplit_inner p v] at h1
      rw [← hΦdef, Φ.apply_symm_apply] at h1
      change w z' + inner ℝ (Φ p).1 z'.1 + inner ℝ (Φ p).2 z'.2
        ≤ w (Φ v) + inner ℝ (Φ p).1 (Φ v).1 + inner ℝ (Φ p).2 (Φ v).2
      linarith
  -- positive measure transfers
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [pos_iff_ne_zero]
  intro h0
  have h1 := null_image_cle volume volume Φ.symm h0
  have e : Φ.symm '' (Φ '' KE) = KE := by
    rw [Set.image_image]; simp
  rw [e] at h1
  exact (ne_of_gt hpos) h1

/-- **The comparison principle for strict subsolutions** of the normalized
`p`-Laplace equation. -/
theorem comparison_strict_full (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p)
    {Ω : Set (EuclSpace d)} (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {U V : EuclSpace d → ℝ}
    (hU : UpperSemicontinuous U) (hV : LowerSemicontinuous V)
    (hUb : BddAbove (range U)) (hVb : BddBelow (range V))
    {c : ℝ} (hc : 0 < c)
    (hsub : IsViscositySubsolution p Ω (fun _ => -c) U)
    (hsup : IsViscositySupersolution p Ω (fun _ => 0) V)
    (hbd : ∀ x ∈ frontier Ω, U x ≤ V x) :
    ∀ x ∈ Ω, U x ≤ V x :=
  comparison_strict_of_J hd hp jensen hΩo hΩb hU hV hUb hVb hc hsub hsup hbd

end

end PLaplacian
