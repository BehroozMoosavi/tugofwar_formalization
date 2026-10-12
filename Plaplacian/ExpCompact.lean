/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.BarrierPoly

/-! # The barrier is a strict discrete supersolution

1. The error in `expansion_uniform` is `o(ε²)`: for every `η > 0` there is a
   radius on which `T_ε φ ≤ φ + ε²/(2(p + d)) Δᴺₚφ + η ε²`. The square-root term
   is at most `H ε² √(A ε)`.
2. On a compact set where `∇φ ≠ 0`, finitely many such radii cover, and the
   bound is uniform.
3. For `v = c + A ψ`, the expansion scales, and `Δᴺₚ` is positively homogeneous.
4. On the compact shell, `Δᴺₚ v ≤ -A`, so for small `ε`,
   `T_ε v ≤ v - A ε²/(4(p + d))`.
-/

open Set Topology Filter Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- **The error is `o(ε²)`, near a point with nonzero gradient.** -/
theorem expansion_small [Nontrivial (EuclSpace d)] (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p)
    (hpd : 0 < p + (d : ℝ)) {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    {x₀ : EuclSpace d} (hx₀ : gradient φ x₀ ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∃ ρ > 0, ∀ y ∈ ball x₀ ρ, ∀ ε : ℝ, 0 < ε → ε ≤ ρ →
      tugOfWarOp p ε φ y ≤ φ y + ε ^ 2 / (2 * (p + (d : ℝ)))
        * normPLapOf p (gradient φ y) (fderiv ℝ (fderiv ℝ φ) y) + η * ε ^ 2 := by
  obtain ⟨ρ₀, hρ₀, H, K, Ka, g, hg, hK, hH, hKa, hexp⟩ := expansion_uniform hd hp hpd hφ hx₀
  set A := 2 * (H + 2 * K) / g with hA
  have hA0 : 0 ≤ A := by positivity
  set ε₁ := min (min ρ₀ 1) (min ((η / (2 * (H + 1))) ^ 2 / (A + 1)) (η / (2 * (K + Ka + 1))))
    with hε₁
  have hε₁0 : 0 < ε₁ := lt_min (lt_min hρ₀ one_pos) (lt_min (by positivity) (by positivity))
  refine ⟨ε₁, hε₁0, fun y hy ε hε hεle => ?_⟩
  have hερ : ε ≤ ρ₀ := le_trans hεle (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε1 : ε ≤ 1 := le_trans hεle (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε2 : ε ≤ (η / (2 * (H + 1))) ^ 2 / (A + 1) :=
    le_trans hεle (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε3 : ε ≤ η / (2 * (K + Ka + 1)) :=
    le_trans hεle (le_trans (min_le_right _ _) (min_le_right _ _))
  have hyρ : y ∈ ball x₀ ρ₀ := ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _)) hy
  obtain ⟨E, hE, hEb⟩ := hexp y hyρ ε hε hερ
  rw [hE]
  -- the square-root term
  set X := 2 * ε * ((H * ε ^ 2 + 2 * K * ε ^ 3) / g) with hX
  have hX0 : 0 ≤ X := by positivity
  have hXA : X ≤ A * ε ^ 3 := by
    have h1 : H * ε ^ 2 + 2 * K * ε ^ 3 ≤ (H + 2 * K) * ε ^ 2 := by
      have : ε ^ 3 ≤ ε ^ 2 := by
        have : ε ^ 3 = ε ^ 2 * ε := by ring
        rw [this]
        calc ε ^ 2 * ε ≤ ε ^ 2 * 1 := mul_le_mul_of_nonneg_left hε1 (by positivity)
          _ = ε ^ 2 := mul_one _
      nlinarith
    have h2 : (H * ε ^ 2 + 2 * K * ε ^ 3) / g ≤ (H + 2 * K) * ε ^ 2 / g :=
      div_le_div_of_nonneg_right h1 hg.le
    have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * ε)
    have e : 2 * ε * ((H + 2 * K) * ε ^ 2 / g) = A * ε ^ 3 := by rw [hA]; field_simp
    linarith
  have hAε : A * ε ≤ (η / (2 * (H + 1))) ^ 2 := by
    have h1 := (le_div_iff₀ (by positivity : (0 : ℝ) < A + 1)).1 hε2
    nlinarith
  have hXsq : X ≤ (η * ε / (2 * (H + 1))) ^ 2 := by
    have h1 : A * ε ^ 3 ≤ (η / (2 * (H + 1))) ^ 2 * ε ^ 2 := by
      have := mul_le_mul_of_nonneg_right hAε (by positivity : (0 : ℝ) ≤ ε ^ 2)
      nlinarith
    have e : (η / (2 * (H + 1))) ^ 2 * ε ^ 2 = (η * ε / (2 * (H + 1))) ^ 2 := by ring
    linarith
  have hsqrt : Real.sqrt X ≤ η * ε / (2 * (H + 1)) := by
    have := Real.sqrt_le_sqrt hXsq
    rwa [Real.sqrt_sq (by positivity)] at this
  have hT1 : H * ε * Real.sqrt X ≤ η / 2 * ε ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left hsqrt (by positivity : (0 : ℝ) ≤ H * ε)
    have h2 : H * ε * (η * ε / (2 * (H + 1))) ≤ η / 2 * ε ^ 2 := by
      rw [show H * ε * (η * ε / (2 * (H + 1))) = (H / (H + 1)) * (η / 2 * ε ^ 2) by
        field_simp]
      have : H / (H + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
      have hpos : 0 ≤ η / 2 * ε ^ 2 := by positivity
      nlinarith
    linarith
  -- the cubic terms
  have hT2 : K * ε ^ 3 + Ka * ε ^ 3 ≤ η / 2 * ε ^ 2 := by
    have h1 : (K + Ka) * ε ≤ η / 2 := by
      have := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (K + Ka + 1))).1 hε3
      nlinarith
    have := mul_le_mul_of_nonneg_right h1 (by positivity : (0 : ℝ) ≤ ε ^ 2)
    nlinarith
  have hEle : E ≤ η * ε ^ 2 := by
    have := le_abs_self E
    linarith
  linarith

/-- **The expansion, uniformly on a compact set with nonzero gradient.** -/
theorem expansion_compact [Nontrivial (EuclSpace d)] (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p)
    (hpd : 0 < p + (d : ℝ)) {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    {K' : Set (EuclSpace d)} (hK' : IsCompact K') (hgrad : ∀ x ∈ K', gradient φ x ≠ 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε₀ > 0, ∀ y ∈ K', ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      tugOfWarOp p ε φ y ≤ φ y + ε ^ 2 / (2 * (p + (d : ℝ)))
        * normPLapOf p (gradient φ y) (fderiv ℝ (fderiv ℝ φ) y) + η * ε ^ 2 := by
  rcases K'.eq_empty_or_nonempty with h | hne
  · exact ⟨1, one_pos, fun y hy => by rw [h] at hy; exact absurd hy (notMem_empty y)⟩
  have hloc : ∀ x ∈ K', ∃ ρ > 0, ∀ y ∈ ball x ρ, ∀ ε : ℝ, 0 < ε → ε ≤ ρ →
      tugOfWarOp p ε φ y ≤ φ y + ε ^ 2 / (2 * (p + (d : ℝ)))
        * normPLapOf p (gradient φ y) (fderiv ℝ (fderiv ℝ φ) y) + η * ε ^ 2 :=
    fun x hx => expansion_small hd hp hpd hφ (hgrad x hx) hη
  choose! ρ hρpos hρ using hloc
  obtain ⟨t, htK, hcover⟩ := hK'.elim_nhds_subcover (fun x => ball x (ρ x))
    (fun x hx => ball_mem_nhds x (hρpos x hx))
  have htne : t.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    have := hcover hy
    rw [mem_iUnion₂] at this
    obtain ⟨x, hx, _⟩ := this
    exact ⟨x, hx⟩
  refine ⟨t.inf' htne ρ, (Finset.lt_inf'_iff htne).2 fun x hx => hρpos x (htK x hx),
    fun y hy ε hε hεle => ?_⟩
  have := hcover hy
  rw [mem_iUnion₂] at this
  obtain ⟨x, hx, hyx⟩ := this
  exact hρ x (htK x hx) y hyx ε hε (le_trans hεle (Finset.inf'_le ρ hx))

/-! ## Scaling -/

theorem peanoAt_affine {f : EuclSpace d → ℝ} {x q : EuclSpace d} {X : Bilin d}
    (h : PeanoAt f x q X) (c A : ℝ) :
    PeanoAt (fun y => c + A * f y) x (A • q) (A • X) := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := h (ε / (|A| + 1)) (by positivity)
  refine ⟨δ, hδ, fun k hk => ?_⟩
  have h1 := hb k hk
  change |(c + A * f (x + k)) - (c + A * f x) - inner ℝ (A • q) k
    - 1 / 2 * ((A • X) k) k| ≤ ε * ‖k‖ ^ 2
  rw [real_inner_smul_left, smul_apply, smul_apply, smul_eq_mul]
  have e : (c + A * f (x + k)) - (c + A * f x) - A * inner ℝ q k - 1 / 2 * (A * (X k) k)
      = A * (f (x + k) - f x - inner ℝ q k - 1 / 2 * (X k) k) := by ring
  rw [e, abs_mul]
  have h2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg A)
  have h3 : |A| * (ε / (|A| + 1) * ‖k‖ ^ 2) ≤ ε * ‖k‖ ^ 2 := by
    have : |A| * (ε / (|A| + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg A]
    have := mul_le_mul_of_nonneg_right this (by positivity : (0 : ℝ) ≤ ‖k‖ ^ 2)
    nlinarith
  linarith

theorem normPLapOf_smul_pos {p A : ℝ} (hA : 0 < A) {q : EuclSpace d} (hq : q ≠ 0)
    (X : Bilin d) : normPLapOf p (A • q) (A • X) = A * normPLapOf p q X := by
  have hqn : 0 < ‖q‖ := norm_pos_iff.2 hq
  unfold normPLapOf infLaplacianOf
  rw [laplacianOf_smul]
  have hn : ‖A • q‖ = A * ‖q‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hA]
  have he : ‖A • q‖⁻¹ • (A • q) = ‖q‖⁻¹ • q := by
    rw [hn, smul_smul]
    congr 1
    field_simp
  rw [he, smul_apply, smul_apply, smul_eq_mul]
  ring

/-! ## The barrier as a strict discrete supersolution -/

/-- The shell around the exterior ball. -/
def bShell (z : EuclSpace d) (δ M : ℝ) : Set (EuclSpace d) :=
  {x | δ ^ 2 ≤ ‖x - z‖ ^ 2 ∧ ‖x - z‖ ^ 2 ≤ δ ^ 2 + 1 / (4 * M)}

theorem isCompact_bShell (z : EuclSpace d) (δ M : ℝ) : IsCompact (bShell z δ M) := by
  have hc : Continuous (fun x : EuclSpace d => ‖x - z‖ ^ 2) := by fun_prop
  apply Metric.isCompact_of_isClosed_isBounded
  · exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨‖z‖ + (δ ^ 2 + 1 / (4 * M) + 1), fun x hx => ?_⟩
    have h1 : ‖x - z‖ ^ 2 ≤ δ ^ 2 + 1 / (4 * M) := hx.2
    have h2 : ‖x - z‖ ≤ ‖x - z‖ ^ 2 + 1 := by nlinarith [norm_nonneg (x - z)]
    have h3 : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
      have := norm_add_le (x - z) z
      rwa [sub_add_cancel] at this
    linarith

/-- **The barrier is a strict discrete supersolution on the shell.** -/
theorem barrier_super [Nontrivial (EuclSpace d)] (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p)
    (hpd : 0 < p + (d : ℝ)) {δ : ℝ} (hδ : 0 < δ) (z : EuclSpace d) (c : ℝ) {A : ℝ}
    (hA : 0 < A) :
    ∃ ε₀ > 0, ∀ y ∈ bShell z δ (bM p δ d), ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      tugOfWarOp p ε (fun x => c + A * bpsi z δ (bM p δ d) x) y
        ≤ (c + A * bpsi z δ (bM p δ d) y) - A * ε ^ 2 / (4 * (p + (d : ℝ))) := by
  set M := bM p δ d with hMdef
  have hp1 : 0 < p - 1 := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hM : 0 < M := by
    rw [hMdef]; unfold bM
    have hD : 0 < (d : ℝ) + p - 2 := by linarith
    exact div_pos (by linarith) (mul_pos (mul_pos (by norm_num) hp1) (pow_pos hδ 2))
  set v : EuclSpace d → ℝ := fun x => c + A * bpsi z δ M x with hvdef
  have hvC : ContDiff ℝ 3 v := contDiff_const.add (contDiff_const.mul (bpsi_contDiff z δ M))
  have hvC2 : ContDiff ℝ 2 v := contDiff_const.add (contDiff_const.mul (bpsi_contDiff z δ M))
  -- the gradient and the operator value of v on the shell
  have hval : ∀ y ∈ bShell z δ M, gradient v y ≠ 0 ∧
      normPLapOf p (gradient v y) (fderiv ℝ (fderiv ℝ v) y) ≤ -A := by
    intro y hy
    obtain ⟨hψg, hψN⟩ := bpsi_op hd hp hδ z hy.1 hy.2
    obtain ⟨hgψ, hNψ⟩ := normPLapOf_of_peano (p := p) (bpsi_contDiff z δ M)
      (bpsi_peano hM.le z δ y)
    obtain ⟨hgv, hNv⟩ := normPLapOf_of_peano (p := p) hvC2
      (peanoAt_affine (bpsi_peano hM.le z δ y) c A)
    set q := (2 * (1 - 2 * M * (‖y - z‖ ^ 2 - δ ^ 2))) • (y - z) with hq
    have hq0 : q ≠ 0 := by rw [← hgψ]; exact hψg
    refine ⟨by rw [hgv]; exact smul_ne_zero hA.ne' hq0, ?_⟩
    change normPLapOf p (gradient v y) (hess v y) ≤ -A
    rw [hNv, normPLapOf_smul_pos hA hq0, ← hNψ]
    have := mul_le_mul_of_nonneg_left hψN hA.le
    linarith
  -- the uniform expansion
  obtain ⟨ε₀, hε₀, hexp⟩ := expansion_compact hd hp hpd hvC (isCompact_bShell z δ M)
    (fun y hy => (hval y hy).1) (η := A / (4 * (p + (d : ℝ)))) (by positivity)
  refine ⟨ε₀, hε₀, fun y hy ε hε hεle => ?_⟩
  have h1 := hexp y hy ε hε hεle
  have h2 := (hval y hy).2
  have h3 : ε ^ 2 / (2 * (p + (d : ℝ))) * normPLapOf p (gradient v y) (fderiv ℝ (fderiv ℝ v) y)
      ≤ ε ^ 2 / (2 * (p + (d : ℝ))) * (-A) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e : ε ^ 2 / (2 * (p + (d : ℝ))) * (-A) + A / (4 * (p + (d : ℝ))) * ε ^ 2
      = -(A * ε ^ 2 / (4 * (p + (d : ℝ)))) := by field_simp; ring
  change tugOfWarOp p ε v y ≤ v y - A * ε ^ 2 / (4 * (p + (d : ℝ)))
  linarith

end

end PLaplacian
