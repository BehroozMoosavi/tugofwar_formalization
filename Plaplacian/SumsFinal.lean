/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.SumsTransfer

@[expose] public section

/-! # The theorem of sums, from Alexandrov's theorem and Jensen's lemma

`TheoremOfSumsRegular` is proved here assuming `AlexandrovThm` and
`JensenLemma`. The assembly:

1. `exists_K_strict` gives the strictified functions `ũ`, `ṽ` with a strict
   global maximum; `dblW0_conv_strict` passes it to their convolutions; and
   `core_sequences` gives points, jets, `Xₙ ≤ Yₙ`, and gradients tending to
   zero.
2. The magic property gives jets of `ũ`, `ṽ` at the maximizers, which
   converge since `xₙ = ξₙ + λ⁻¹ aₙ`.
3. Symmetrizing makes the bounded quadratic forms bounded entrywise, and two
   extractions give limit forms with `X ≤ Y`.
4. The transfer lemmas give jets of `u` and `v`, and the closed jets follow,
   the values converging by continuity of the semiconvex convolutions.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



set_option synthInstance.maxHeartbeats 400000 in
-- Instance search on iterated continuous linear maps needs a larger budget.
/-- Norm convergence of forms gives convergence of the quadratic form. -/
theorem tendsto_form_apply {Xs : ℕ → Bilin d} {X : Bilin d}
    (h : Tendsto (fun n => ‖Xs n - X‖) atTop (𝓝 0)) (w : EuclSpace d) :
    Tendsto (fun n => (Xs n w) w) atTop (𝓝 ((X w) w)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hg : Tendsto (fun n => ‖Xs n - X‖ * (‖w‖ * ‖w‖)) atTop (𝓝 0) := by
    have := h.mul_const (‖w‖ * ‖w‖)
    rwa [zero_mul] at this
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hg
  rw [← form_sub_apply]
  calc ‖((Xs n - X) w) w‖ ≤ ‖(Xs n - X) w‖ * ‖w‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖Xs n - X‖ * ‖w‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ = ‖Xs n - X‖ * (‖w‖ * ‖w‖) := by ring

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search on iterated continuous linear maps needs a larger budget.
/-- The quartic's form term tends to zero in norm. -/
theorem tendsto_norm_quartic_form {K : ℝ} {xs : ℕ → EuclSpace d}
    (hxs : Tendsto xs atTop (𝓝 0)) :
    Tendsto (fun n => ‖K‖ * (‖12 * ‖xs n‖ ^ 2‖ * ‖idForm d‖)) atTop (𝓝 0) := by
  have hc : Tendsto (fun n => 12 * ‖xs n‖ ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_quartic_coef (c := 0) hxs
  have := (hc.norm.mul_const ‖idForm d‖).const_mul ‖K‖
  simpa using this

section closed

variable {u v : EuclSpace d → ℝ} {q xh yh : EuclSpace d} {K : ℝ}

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search on iterated continuous linear maps needs a larger budget.
/-- **The closed superjet of `u`**, from jets of `ũ` at points tending to
zero. -/
theorem clSuperJet_u_of (hK : 0 ≤ K) {xs as : ℕ → EuclSpace d} {As : ℕ → Bilin d}
    {Xl : Bilin d}
    (hj : ∀ n, (as n, As n) ∈ SuperJet (uTilde u q xh K) (xs n))
    (hxs : Tendsto xs atTop (𝓝 0)) (has : Tendsto as atTop (𝓝 0))
    (hAs : Tendsto (fun n => ‖As n - Xl‖) atTop (𝓝 0))
    (hval : Tendsto (fun n => uTilde u q xh K (xs n)) atTop (𝓝 0)) :
    (q, Xl) ∈ ClSuperJet u xh := by
  refine ⟨fun n => xh + xs n, fun n => as n + K • ((4 * ‖xs n‖ ^ 2) • xs n) + q,
    fun n => As n + K • ((12 * ‖xs n‖ ^ 2) • idForm d),
    fun n => superJet_u_of_uTilde hK (hj n), ?_, ?_, ?_, ?_⟩
  · -- the points
    have := tendsto_const_nhds (x := xh) |>.add hxs
    simpa using this
  · -- the values
    have e : (fun n => u (xh + xs n)) = fun n => uTilde u q xh K (xs n)
        + inner ℝ q (xh + xs n) + K * ‖xs n‖ ^ 4 + (u xh - inner ℝ q xh) :=
      funext fun n => u_apply_eq u q xh K (xs n)
    rw [e]
    have h1 : Tendsto (fun n => inner ℝ q (xh + xs n)) atTop
        (𝓝 (inner ℝ q (xh + 0))) :=
      ((continuous_const.inner (continuous_const.add continuous_id)).tendsto 0).comp hxs
    have h2 : Tendsto (fun n => K * ‖xs n‖ ^ 4) atTop (𝓝 (K * ‖(0 : EuclSpace d)‖ ^ 4)) :=
      ((hxs.norm).pow 4).const_mul K
    have h3 := ((hval.add h1).add h2).add
      (tendsto_const_nhds (x := u xh - inner ℝ q xh))
    have hlim : 0 + inner ℝ q (xh + 0) + K * ‖(0 : EuclSpace d)‖ ^ 4
        + (u xh - inner ℝ q xh) = u xh := by
      rw [add_zero, norm_zero]; ring
    rw [hlim] at h3
    exact h3
  · -- the gradients
    have hg : Tendsto (fun n => (4 * ‖xs n‖ ^ 2) • xs n) atTop (𝓝 0) := by
      simpa using tendsto_quartic_grad (c := 0) hxs
    have := (has.add (hg.const_smul K)).add (tendsto_const_nhds (x := q))
    simpa using this
  · -- the forms
    have hb : ∀ n, ‖(As n + K • ((12 * ‖xs n‖ ^ 2) • idForm d)) - Xl‖
        ≤ ‖As n - Xl‖ + ‖K‖ * (‖12 * ‖xs n‖ ^ 2‖ * ‖idForm d‖) := by
      intro n
      have e : (As n + K • ((12 * ‖xs n‖ ^ 2) • idForm d)) - Xl
          = (As n - Xl) + K • ((12 * ‖xs n‖ ^ 2) • idForm d) := by abel
      rw [e]
      refine (ContinuousLinearMap.opNorm_add_le _ _).trans ?_
      have h1 := ContinuousLinearMap.opNorm_smul_le K ((12 * ‖xs n‖ ^ 2) • idForm d)
      have h2 := ContinuousLinearMap.opNorm_smul_le (12 * ‖xs n‖ ^ 2) (idForm d)
      have hK' : 0 ≤ ‖K‖ := norm_nonneg _
      have h3 := mul_le_mul_of_nonneg_left h2 hK'
      linarith
    have hR := hAs.add (tendsto_norm_quartic_form (K := K) hxs)
    rw [add_zero] at hR
    exact squeeze_zero (fun n => ContinuousLinearMap.opNorm_nonneg _) hb hR

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search on iterated continuous linear maps needs a larger budget.
/-- **The closed subjet of `v`**, from jets of `ṽ` at points tending to zero. -/
theorem clSubJet_v_of (hK : 0 ≤ K) {ys bs : ℕ → EuclSpace d} {Bs : ℕ → Bilin d}
    {Yl : Bilin d}
    (hj : ∀ n, (bs n, Bs n) ∈ SubJet (vTilde v q yh K) (ys n))
    (hys : Tendsto ys atTop (𝓝 0)) (hbs : Tendsto bs atTop (𝓝 0))
    (hBs : Tendsto (fun n => ‖Bs n - Yl‖) atTop (𝓝 0))
    (hval : Tendsto (fun n => vTilde v q yh K (ys n)) atTop (𝓝 0)) :
    (q, Yl) ∈ ClSubJet v yh := by
  refine ⟨fun n => yh + ys n, fun n => bs n + K • (-((4 * ‖ys n‖ ^ 2) • ys n)) + q,
    fun n => Bs n + K • (-((12 * ‖ys n‖ ^ 2) • idForm d)),
    fun n => subJet_v_of_vTilde hK (hj n), ?_, ?_, ?_, ?_⟩
  · have := tendsto_const_nhds (x := yh) |>.add hys
    simpa using this
  · have e : (fun n => v (yh + ys n)) = fun n => vTilde v q yh K (ys n)
        + inner ℝ q (yh + ys n) - K * ‖ys n‖ ^ 4 + (v yh - inner ℝ q yh) :=
      funext fun n => v_apply_eq v q yh K (ys n)
    rw [e]
    have h1 : Tendsto (fun n => inner ℝ q (yh + ys n)) atTop
        (𝓝 (inner ℝ q (yh + 0))) :=
      ((continuous_const.inner (continuous_const.add continuous_id)).tendsto 0).comp hys
    have h2 : Tendsto (fun n => K * ‖ys n‖ ^ 4) atTop (𝓝 (K * ‖(0 : EuclSpace d)‖ ^ 4)) :=
      ((hys.norm).pow 4).const_mul K
    have h3 := ((hval.add h1).sub h2).add
      (tendsto_const_nhds (x := v yh - inner ℝ q yh))
    have hlim : 0 + inner ℝ q (yh + 0) - K * ‖(0 : EuclSpace d)‖ ^ 4
        + (v yh - inner ℝ q yh) = v yh := by
      rw [add_zero, norm_zero]; ring
    rw [hlim] at h3
    exact h3
  · have hg : Tendsto (fun n => (4 * ‖ys n‖ ^ 2) • ys n) atTop (𝓝 0) := by
      simpa using tendsto_quartic_grad (c := 0) hys
    have := (hbs.add (hg.neg.const_smul K)).add (tendsto_const_nhds (x := q))
    simpa using this
  · have hb : ∀ n, ‖(Bs n + K • (-((12 * ‖ys n‖ ^ 2) • idForm d))) - Yl‖
        ≤ ‖Bs n - Yl‖ + ‖K‖ * (‖12 * ‖ys n‖ ^ 2‖ * ‖idForm d‖) := by
      intro n
      have e : (Bs n + K • (-((12 * ‖ys n‖ ^ 2) • idForm d))) - Yl
          = (Bs n - Yl) + K • (-((12 * ‖ys n‖ ^ 2) • idForm d)) := by abel
      rw [e]
      refine (ContinuousLinearMap.opNorm_add_le _ _).trans ?_
      have h1 := ContinuousLinearMap.opNorm_smul_le K (-((12 * ‖ys n‖ ^ 2) • idForm d))
      rw [ContinuousLinearMap.opNorm_neg] at h1
      have h2 := ContinuousLinearMap.opNorm_smul_le (12 * ‖ys n‖ ^ 2) (idForm d)
      have hK' : 0 ≤ ‖K‖ := norm_nonneg _
      have h3 := mul_le_mul_of_nonneg_left h2 hK'
      linarith
    have hR := hBs.add (tendsto_norm_quartic_form (K := K) hys)
    rw [add_zero] at hR
    exact squeeze_zero (fun n => ContinuousLinearMap.opNorm_nonneg _) hb hR

end closed

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search on iterated continuous linear maps needs a larger budget.
/-- Entry bound for a symmetrized form with bounded quadratic form. -/
theorem symmForm_entry_le {X : Bilin d} {L : ℝ} (hL : 0 ≤ L)
    (hX : ∀ w, |(X w) w| ≤ L * ‖w‖ ^ 2) (i j : Fin d) :
    |(symmForm X (obasis d i)) (obasis d j)| ≤ L := by
  have h := symmForm_le_mul hL hX (obasis d i) (obasis d j)
  rw [(obasis d).orthonormal.1 i, (obasis d).orthonormal.1 j, mul_one, mul_one] at h
  exact h

set_option maxHeartbeats 2000000 in
-- The assembly applies a dozen results in one declaration.
set_option synthInstance.maxHeartbeats 400000 in
-- Instance search on iterated continuous linear maps needs a larger budget.
/-- **The regular half of the theorem of sums**, from Alexandrov's theorem and
Jensen's lemma. -/
theorem theoremOfSumsRegular_of (hA : AlexandrovThm d) (hJ : JensenLemma d) :
    TheoremOfSumsRegular d := by
  intro u v hu hv hub hvb α hα xh yh _hne hmax
  set q := (‖xh - yh‖ ^ 2 / α) • (xh - yh) with hqdef
  obtain ⟨K, hK, hΨ⟩ := exists_K_strict hα hub hvb hmax
  have hK0 : 0 ≤ K := by have := norm_nonneg q; linarith
  set uT := uTilde u q xh K with huT
  set vT := vTilde v q yh K with hvT
  have hu0 : uT 0 = 0 := uTilde_zero
  have hv0 : vT 0 = 0 := vTilde_zero
  have huu : UpperSemicontinuous uT := usc_uTilde hu
  have hub' : BddAbove (range uT) := bddAbove_uTilde hK hub
  have hvv : UpperSemicontinuous (fun y => -vT y) := usc_neg_vTilde hv
  have hvb' : BddAbove (range (fun y => -vT y)) := bddAbove_neg_vTilde hK hvb
  set h0 := xh - yh with hh0
  set L := lamC α h0 with hLdef
  have hL : 0 < L := lamC_pos hα h0
  set U := supConv L uT with hUdef
  set N := supConv L (fun y => -vT y) with hNdef
  have hstrict := dblW0_conv_strict (h0 := h0) hα hu0 hv0 huu hub' hvv hvb' hΨ
  obtain ⟨hU0, hN0⟩ := supConv_zero (h0 := h0) hα hu0 hv0 hub' hvb' hΨ
  have hU0' : U 0 = 0 := hU0
  have hN0' : N 0 = 0 := hN0
  -- the core
  obtain ⟨ξs, ζs, as, bs, Xs, Ys, hsup, hsub, hξ, hζ, ha, hb, hle, hXl, hYu⟩ :=
    core_sequences (u := U) (v := fun ζ => -N ζ) hA hJ hL
      (semiconvex_uconv hα hub') (semiconvex_vconv hα hvb') zero_le_one
      (by norm_num) hα hstrict
  -- the maximizers, and the jets of ũ there
  have hxe : ∀ n, ∃ x, U (ξs n) = uT x - L / 2 * ‖x - ξs n‖ ^ 2 :=
    fun n => supConv_attained hL huu hub' (ξs n)
  choose xs hxs using hxe
  have hjU : ∀ n, (as n, Xs n) ∈ SuperJet uT (xs n) :=
    fun n => superJet_of_supConv hL.le hub' (hxs n) (hsup n)
  have hgU : ∀ n, as n = L • (xs n - ξs n) :=
    fun n => supConv_grad hL.le hub' (hxs n) (hsup n)
  -- the maximizers, and the jets of ṽ there
  have hye : ∀ n, ∃ y, N (ζs n) = -vT y - L / 2 * ‖y - ζs n‖ ^ 2 :=
    fun n => supConv_attained hL hvv hvb' (ζs n)
  choose ys hys using hye
  have hsupN : ∀ n, (-(bs n), -(Ys n)) ∈ SuperJet N (ζs n) :=
    fun n => superJet_congr (by funext y; simp) (superJet_neg_of_subJet (hsub n))
  have hjN : ∀ n, (-(bs n), -(Ys n)) ∈ SuperJet (fun y => -vT y) (ys n) :=
    fun n => superJet_of_supConv hL.le hvb' (hys n) (hsupN n)
  have hgN : ∀ n, -(bs n) = L • (ys n - ζs n) :=
    fun n => supConv_grad hL.le hvb' (hys n) (hsupN n)
  have hjV : ∀ n, (bs n, Ys n) ∈ SubJet vT (ys n) := by
    intro n
    have h1 := subJet_neg_of_superJet (hjN n)
    have eY : - -Ys n = Ys n := by ext x y; simp
    rw [neg_neg, eY] at h1
    exact subJet_congr (by funext y; simp) h1
  -- the maximizers converge
  have hdU : ∀ n, xs n - ξs n = L⁻¹ • as n := by
    intro n; rw [hgU n, smul_smul, inv_mul_cancel₀ hL.ne', one_smul]
  have hdV : ∀ n, ys n - ζs n = L⁻¹ • -(bs n) := by
    intro n; rw [hgN n, smul_smul, inv_mul_cancel₀ hL.ne', one_smul]
  have hxsT : Tendsto xs atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ξs n + L⁻¹ • as n) atTop (𝓝 (0 + L⁻¹ • 0)) :=
      hξ.add (ha.const_smul L⁻¹)
    rw [smul_zero, add_zero] at h1
    refine h1.congr (fun n => ?_)
    rw [← hdU n]; abel
  have hysT : Tendsto ys atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ζs n + L⁻¹ • -(bs n)) atTop (𝓝 (0 + L⁻¹ • -0)) :=
      hζ.add (hb.neg.const_smul L⁻¹)
    rw [neg_zero, smul_zero, add_zero] at h1
    refine h1.congr (fun n => ?_)
    rw [← hdV n]; abel
  -- the values converge
  have hUc : Continuous U := semiconvex_continuous (semiconvex_uconv (h0 := h0) hα hub')
  have hNc : Continuous N := semiconvex_continuous (semiconvex_supConv hL.le hvb')
  have hvalU : Tendsto (fun n => uT (xs n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => U (ξs n)) atTop (𝓝 0) := by
      have := (hUc.tendsto 0).comp hξ
      rw [hU0'] at this
      exact this
    have h2 : Tendsto (fun n => L / 2 * ‖L⁻¹ • as n‖ ^ 2) atTop (𝓝 0) := by
      have := (((ha.const_smul L⁻¹).norm).pow 2).const_mul (L / 2)
      simpa using this
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr (fun n => ?_)
    have := hxs n
    rw [hdU n] at this
    linarith
  have hvalV : Tendsto (fun n => vT (ys n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => N (ζs n)) atTop (𝓝 0) := by
      have := (hNc.tendsto 0).comp hζ
      rw [hN0'] at this
      exact this
    have h2 : Tendsto (fun n => L / 2 * ‖L⁻¹ • -(bs n)‖ ^ 2) atTop (𝓝 0) := by
      have := (((hb.neg.const_smul L⁻¹).norm).pow 2).const_mul (L / 2)
      simpa using this
    have h3 := (h1.add h2).neg
    rw [add_zero, neg_zero] at h3
    refine h3.congr (fun n => ?_)
    have := hys n
    rw [hdV n] at this
    linarith
  -- symmetrize, and bound the entries
  have habsX : ∀ n w, |(Xs n w) w| ≤ L * ‖w‖ ^ 2 := fun n w =>
    abs_le.2 ⟨by linarith [hXl n w], (hle n w).trans (hYu n w)⟩
  have habsY : ∀ n w, |(Ys n w) w| ≤ L * ‖w‖ ^ 2 := fun n w =>
    abs_le.2 ⟨by linarith [hXl n w, hle n w], hYu n w⟩
  have hjU' : ∀ n, (as n, symmForm (Xs n)) ∈ SuperJet uT (xs n) :=
    fun n => superJet_symmForm (hjU n)
  have hjV' : ∀ n, (bs n, symmForm (Ys n)) ∈ SubJet vT (ys n) :=
    fun n => subJet_symmForm (hjV n)
  -- two extractions
  obtain ⟨Xl, φ, hφ, hXconv⟩ := exists_subseq_form (fun n => symmForm (Xs n))
    (fun n i j => symmForm_entry_le hL.le (habsX n) i j)
  obtain ⟨Yl, ψ, hψ, hYconv⟩ := exists_subseq_form (fun n => symmForm (Ys (φ n)))
    (fun n i j => symmForm_entry_le hL.le (habsY (φ n)) i j)
  have hσ : StrictMono (fun n => φ (ψ n)) := hφ.comp hψ
  have hσT := hσ.tendsto_atTop
  have hXconv' : Tendsto (fun n => ‖symmForm (Xs (φ (ψ n))) - Xl‖) atTop (𝓝 0) :=
    hXconv.comp hψ.tendsto_atTop
  refine ⟨Xl, Yl, ?_, ?_, ?_⟩
  · -- the closed superjet of u
    exact clSuperJet_u_of hK0 (fun n => hjU' (φ (ψ n))) (hxsT.comp hσT)
      (ha.comp hσT) hXconv' (hvalU.comp hσT)
  · -- the closed subjet of v
    exact clSubJet_v_of hK0 (fun n => hjV' (φ (ψ n))) (hysT.comp hσT)
      (hb.comp hσT) hYconv (hvalV.comp hσT)
  · -- X ≤ Y in the limit
    intro w
    have h1 := tendsto_form_apply hXconv' w
    have h2 := tendsto_form_apply hYconv w
    refine le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun n => ?_)
    have := quadLE_symmForm (hle (φ (ψ n))) w
    exact this

set_option synthInstance.maxHeartbeats 400000 in
-- Instance search on iterated continuous linear maps needs a larger budget.
/-- **The comparison principle for strict subsolutions**, from Alexandrov's
theorem and Jensen's lemma. -/
theorem comparison_strict_of_AJ (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p)
    (hA : AlexandrovThm d) (hJ : JensenLemma d) {Ω : Set (EuclSpace d)}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) {U V : EuclSpace d → ℝ}
    (hU : UpperSemicontinuous U) (hV : LowerSemicontinuous V)
    (hUb : BddAbove (range U)) (hVb : BddBelow (range V))
    {c : ℝ} (hc : 0 < c)
    (hsub : IsViscositySubsolution p Ω (fun _ => -c) U)
    (hsup : IsViscositySupersolution p Ω (fun _ => 0) V)
    (hbd : ∀ x ∈ frontier Ω, U x ≤ V x) :
    ∀ x ∈ Ω, U x ≤ V x :=
  comparison_strict_of_regular hd hp (theoremOfSumsRegular_of hA hJ) hΩo hΩb hU hV
    hUb hVb hc hsub hsup hbd

end

end PLaplacian
