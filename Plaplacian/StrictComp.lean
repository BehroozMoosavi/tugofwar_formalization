/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.ClJetBridge

/-! # The comparison principle for strict subsolutions

A bounded upper semicontinuous strict subsolution, with generator at most
`-c < 0`, lies below a bounded lower semicontinuous supersolution in a bounded
open set, if it does on the boundary. The proof assumes the theorem of sums,
stated as `TheoremOfSums` and to be proved separately.

## Doubling

If `U(x₀) > V(x₀)` somewhere in `Ω`, maximize
`Φ_α(x, y) = U(x) - V(y) - ‖x - y‖⁴ / (4α)` over the compact set
`Ω̄ × Ω̄`. The maximizers stay within `O(α^{1/4})` of each other; a subsequence
converges to a diagonal point `(z, z)`; semicontinuity gives
`U(z) - V(z) ≥ U(x₀) - V(x₀) > 0`, so `z` is not on the boundary, where
`U ≤ V`; hence for small `α` both maximizers are interior.

## The contradiction

At an interior maximizer the theorem of sums gives forms `X ≤ Y` in the closed
jets. If the maximizers differ, the gradient of the penalty is nonzero, and
`F(q,X) ≤ -c`, `0 ≤ F(q,Y)`, and ellipticity `F(q,Y) ≤ F(q,X)` are
incompatible. If they coincide, the gradient vanishes, the quartic gives
`X ≤ 0`, and then `0 ≤ F_*(X) ≤ -c`.

## Scope

Strictness is used in both cases. Passing from a non-strict subsolution to a
strict one is the delicate step for the homogeneous normalized p-Laplacian:
adding a quadratic shifts the gradient, which the operator sees through its
direction. That step is not taken here.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- The doubled functional. -/
def dblPhi (U V : EuclSpace d → ℝ) (α : ℝ) (z : EuclSpace d × EuclSpace d) : ℝ :=
  U z.1 - V z.2 - ‖z.1 - z.2‖ ^ 4 / (4 * α)

theorem usc_dblPhi {U V : EuclSpace d → ℝ} (hU : UpperSemicontinuous U)
    (hV : LowerSemicontinuous V) (α : ℝ) : UpperSemicontinuous (dblPhi U V α) := by
  have h1 : UpperSemicontinuous (fun z : EuclSpace d × EuclSpace d => U z.1) :=
    hU.comp continuous_fst
  have h2 : UpperSemicontinuous (fun z : EuclSpace d × EuclSpace d => -V z.2) :=
    hV.neg.comp continuous_snd
  have h3 : UpperSemicontinuous
      (fun z : EuclSpace d × EuclSpace d => -(‖z.1 - z.2‖ ^ 4 / (4 * α))) := by
    apply Continuous.upperSemicontinuous
    fun_prop
  have heq : dblPhi U V α
      = fun z => U z.1 + -V z.2 + -(‖z.1 - z.2‖ ^ 4 / (4 * α)) := by
    funext z; unfold dblPhi; ring
  rw [heq]
  exact (h1.add h2).add h3

/-- **The doubling lemma.** -/
theorem exists_interior_max {Ω : Set (EuclSpace d)} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {U V : EuclSpace d → ℝ}
    (hU : UpperSemicontinuous U) (hV : LowerSemicontinuous V)
    (hUb : BddAbove (range U)) (hVb : BddBelow (range V))
    (hbd : ∀ x ∈ frontier Ω, U x ≤ V x) {x₀ : EuclSpace d} (hx₀ : x₀ ∈ Ω)
    (hpos : V x₀ < U x₀) :
    ∃ α > 0, ∃ xh ∈ Ω, ∃ yh ∈ Ω,
      IsMaxOn (dblPhi U V α) (closure Ω ×ˢ closure Ω) (xh, yh) := by
  set K := closure Ω ×ˢ closure Ω with hKdef
  have hKc : IsCompact K := hΩb.isCompact_closure.prod hΩb.isCompact_closure
  have hx₀K : (x₀, x₀) ∈ K := ⟨subset_closure hx₀, subset_closure hx₀⟩
  -- a maximizer for each parameter 1/(n+1)
  have hex : ∀ n : ℕ, ∃ z ∈ K, IsMaxOn (dblPhi U V (1 / ((n : ℝ) + 1))) K z :=
    fun n => ((usc_dblPhi hU hV _).upperSemicontinuousOn K).exists_isMaxOn
      ⟨_, hx₀K⟩ hKc
  choose z hzK hzmax using hex
  set m := U x₀ - V x₀ with hm
  have hmpos : 0 < m := by rw [hm]; linarith
  obtain ⟨SU, hSU⟩ := hUb
  obtain ⟨IV, hIV⟩ := hVb
  have hUle : ∀ x, U x ≤ SU := fun x => hSU ⟨x, rfl⟩
  have hVge : ∀ y, IV ≤ V y := fun y => hIV ⟨y, rfl⟩
  -- the value at each maximizer is at least m
  have hval : ∀ n : ℕ, m ≤ dblPhi U V (1 / ((n : ℝ) + 1)) (z n) := fun n => by
    have h1 : dblPhi U V (1 / ((n : ℝ) + 1)) (x₀, x₀)
        ≤ dblPhi U V (1 / ((n : ℝ) + 1)) (z n) := hzmax n hx₀K
    have h0 : dblPhi U V (1 / ((n : ℝ) + 1)) (x₀, x₀) = m := by
      simp [dblPhi, hm]
    linarith
  -- the penalty is bounded
  have hpen : ∀ n, ‖(z n).1 - (z n).2‖ ^ 4
      ≤ (SU - IV - m) * (4 * (1 / ((n : ℝ) + 1))) := fun n => by
    have h1 := hval n
    have h2 := hUle (z n).1
    have h3 := hVge (z n).2
    unfold dblPhi at h1
    have h4α : (0 : ℝ) < 4 * (1 / ((n : ℝ) + 1)) := by positivity
    have hq : ‖(z n).1 - (z n).2‖ ^ 4 / (4 * (1 / ((n : ℝ) + 1)))
        ≤ SU - IV - m := by linarith
    exact (div_le_iff₀ h4α).1 hq
  -- a convergent subsequence
  obtain ⟨a, haK, φ, hφ, hlim⟩ := hKc.tendsto_subseq hzK
  have hlim1 : Tendsto (fun n => (z (φ n)).1) atTop (𝓝 a.1) :=
    (continuous_fst.tendsto a).comp hlim
  have hlim2 : Tendsto (fun n => (z (φ n)).2) atTop (𝓝 a.2) :=
    (continuous_snd.tendsto a).comp hlim
  -- the limit is on the diagonal
  have hdiag : a.1 = a.2 := by
    have hT : Tendsto (fun n => ‖(z (φ n)).1 - (z (φ n)).2‖ ^ 4) atTop
        (𝓝 (‖a.1 - a.2‖ ^ 4)) := ((hlim1.sub hlim2).norm).pow 4
    have hB : Tendsto (fun n => (SU - IV - m) * (4 * (1 / ((φ n : ℝ) + 1))))
        atTop (𝓝 0) := by
      have h := ((tendsto_one_div_add_atTop_nhds_zero_nat.comp
        hφ.tendsto_atTop).const_mul 4).const_mul (SU - IV - m)
      rw [show (SU - IV - m) * (4 * (0 : ℝ)) = 0 by ring] at h
      exact h
    have hle : ‖a.1 - a.2‖ ^ 4 ≤ 0 :=
      le_of_tendsto_of_tendsto hT hB (Eventually.of_forall fun n => hpen (φ n))
    have h0 : (0 : ℝ) ≤ ‖a.1 - a.2‖ ^ 4 := by positivity
    have h4 : ‖a.1 - a.2‖ ^ 4 = 0 := le_antisymm hle h0
    have hn : ‖a.1 - a.2‖ = 0 := (pow_eq_zero_iff (by norm_num)).1 h4
    exact sub_eq_zero.1 (norm_eq_zero.1 hn)
  -- the limit value is at least m
  have hlimval : m ≤ U a.1 - V a.2 := by
    by_contra h
    push Not at h
    set ε := (m - (U a.1 - V a.2)) / 2 with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; linarith
    have hu : ∀ᶠ n in atTop, U (z (φ n)).1 < U a.1 + ε :=
      hlim1.eventually (hU a.1 (U a.1 + ε) (by linarith))
    have hv : ∀ᶠ n in atTop, V a.2 - ε < V (z (φ n)).2 :=
      hlim2.eventually (hV a.2 (V a.2 - ε) (by linarith))
    obtain ⟨n, hn1, hn2⟩ := (hu.and hv).exists
    have h1 := hval (φ n)
    have hpen0 : (0 : ℝ) ≤ ‖(z (φ n)).1 - (z (φ n)).2‖ ^ 4
        / (4 * (1 / ((φ n : ℝ) + 1))) := by positivity
    unfold dblPhi at h1
    linarith
  -- so the limit point is interior
  have ha1Ω : a.1 ∈ Ω := by
    have ha1K : a.1 ∈ closure Ω := haK.1
    rw [closure_eq_self_union_frontier] at ha1K
    rcases ha1K with h | h
    · exact h
    · exfalso
      have hb := hbd a.1 h
      rw [← hdiag] at hlimval
      linarith
  have ha2Ω : a.2 ∈ Ω := hdiag ▸ ha1Ω
  -- and so, eventually, are the maximizers
  have hev1 : ∀ᶠ n in atTop, (z (φ n)).1 ∈ Ω := hlim1 (hΩo.mem_nhds ha1Ω)
  have hev2 : ∀ᶠ n in atTop, (z (φ n)).2 ∈ Ω := hlim2 (hΩo.mem_nhds ha2Ω)
  obtain ⟨n, hn1, hn2⟩ := (hev1.and hev2).exists
  exact ⟨1 / ((φ n : ℝ) + 1), by positivity, (z (φ n)).1, hn1, (z (φ n)).2, hn2,
    hzmax (φ n)⟩

/-- A maximum over the closed product at an interior pair is a local
maximum. -/
theorem isLocalMax_of_interior {F : EuclSpace d × EuclSpace d → ℝ}
    {Ω : Set (EuclSpace d)} (hΩo : IsOpen Ω) {xh yh : EuclSpace d}
    (hx : xh ∈ Ω) (hy : yh ∈ Ω)
    (hmax : IsMaxOn F (closure Ω ×ˢ closure Ω) (xh, yh)) :
    IsLocalMax F (xh, yh) := by
  apply hmax.isLocalMax
  have h : Ω ×ˢ Ω ∈ 𝓝 (xh, yh) := (hΩo.prod hΩo).mem_nhds ⟨hx, hy⟩
  exact Filter.mem_of_superset h (Set.prod_mono subset_closure subset_closure)

/-- Away from the diagonal the gradient of the penalty is nonzero. -/
theorem penaltyGrad_ne_zero {α : ℝ} (hα : 0 < α) {x y : EuclSpace d}
    (h : x ≠ y) : penaltyGrad α x y ≠ 0 := by
  unfold penaltyGrad
  have hxy : x - y ≠ 0 := sub_ne_zero.2 h
  have hn : 0 < ‖x - y‖ := norm_pos_iff.2 hxy
  exact smul_ne_zero (by positivity) hxy

/-- **The comparison principle for strict subsolutions**, assuming the theorem
of sums. -/
theorem comparison_strict (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p)
    (hTS : TheoremOfSums d) {Ω : Set (EuclSpace d)} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {U V : EuclSpace d → ℝ}
    (hU : UpperSemicontinuous U) (hV : LowerSemicontinuous V)
    (hUb : BddAbove (range U)) (hVb : BddBelow (range V))
    {c : ℝ} (hc : 0 < c)
    (hsub : IsViscositySubsolution p Ω (fun _ => -c) U)
    (hsup : IsViscositySupersolution p Ω (fun _ => 0) V)
    (hbd : ∀ x ∈ frontier Ω, U x ≤ V x) :
    ∀ x ∈ Ω, U x ≤ V x := by
  intro x₀ hx₀
  by_contra hlt
  push Not at hlt
  obtain ⟨α, hα, xh, hxh, yh, hyh, hmax⟩ :=
    exists_interior_max hΩo hΩb hU hV hUb hVb hbd hx₀ hlt
  have hloc := isLocalMax_of_interior hΩo hxh hyh hmax
  obtain ⟨X, Y, hX, hY, hXY, hsing⟩ := hTS U V hU hV hUb hVb α hα xh yh hloc
  by_cases heq : xh = yh
  · -- the singular case
    have hq0 : penaltyGrad α xh yh = 0 := by rw [heq, penaltyGrad_self]
    rw [hq0] at hX
    have h1 := clSuperJet_singular hd hp hΩo hsub hxh hX
    have h2 := viscFLower_nonneg_of_nonpos hd hp (hsing heq).1
    linarith
  · -- the regular case
    have hq := penaltyGrad_ne_zero hα heq
    have h1 := clSuperJet_regular hd hp hΩo hsub hxh hX hq
    have h2 := clSubJet_regular hd hp hΩo hsup hyh hY hq
    have h3 := viscF_anti hp hXY (penaltyGrad α xh yh)
    linarith

end

end PLaplacian
