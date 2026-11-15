/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Step3

@[expose] public section

/-! # The regularized pair

`U_λ = supConv λ U` and `V_λ = -supConv λ (-V)`.

1. Bounds: `U ≤ U_λ`, `S_L ≤ U_λ ≤ S_U`; `V_λ ≤ V`, `T_L ≤ V_λ ≤ T_U`.
2. `U_λ` is semiconvex and `V_λ` semiconcave, since `-V_λ = supConv λ (-V)`; both
   are continuous.
3. At `ξ` with `B(ξ, ρ) ⊆ Ω` and `ρ² > 2·osc/λ`, superjets of `U_λ` satisfy the
   subsolution inequality; so do superjets of `-V_λ`, since `-V` is a
   subsolution and the magic property applies to its sup-convolution.
-/

open Set Topology Filter Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- The regularized subsolution. -/
def regU (lam : ℝ) (U : EuclSpace d → ℝ) : EuclSpace d → ℝ := supConv lam U

/-- The regularized supersolution. -/
def regV (lam : ℝ) (V : EuclSpace d → ℝ) : EuclSpace d → ℝ :=
  fun ξ => -supConv lam (fun y => -V y) ξ

/-! ## Semicontinuity and bounds of `-V` -/

theorem usc_neg_of_lsc {V : EuclSpace d → ℝ} (hV : LowerSemicontinuous V) :
    UpperSemicontinuous (fun y => -V y) := by
  intro x c hc
  have := hV x (-c) (by linarith)
  exact this.mono fun y hy => by linarith

theorem bddAbove_neg_of_bddBelow {V : EuclSpace d → ℝ} (hVb : BddBelow (range V)) :
    BddAbove (range (fun y => -V y)) := by
  obtain ⟨m, hm⟩ := hVb
  refine ⟨-m, ?_⟩
  rintro _ ⟨y, rfl⟩
  have := hm ⟨y, rfl⟩
  linarith

theorem neg_regV (lam : ℝ) (V : EuclSpace d → ℝ) :
    (fun z => -regV lam V z) = supConv lam (fun y => -V y) := by
  funext z
  simp [regV]

/-! ## Bounds -/

theorem regU_bounds {lam : ℝ} (hlam : 0 ≤ lam) {U : EuclSpace d → ℝ}
    (hUb : BddAbove (range U)) {SU SL : ℝ} (hSU : ∀ x, U x ≤ SU) (hSL : ∀ x, SL ≤ U x)
    (ξ : EuclSpace d) :
    U ξ ≤ regU lam U ξ ∧ regU lam U ξ ≤ SU ∧ SL ≤ regU lam U ξ := by
  have h1 := self_le_supConv hlam hUb ξ
  have h2 := supConv_le_bound hlam hSU ξ
  exact ⟨h1, h2, le_trans (hSL ξ) h1⟩

theorem regV_bounds {lam : ℝ} (hlam : 0 ≤ lam) {V : EuclSpace d → ℝ}
    (hVb : BddBelow (range V)) {TU TL : ℝ} (hTU : ∀ x, V x ≤ TU) (hTL : ∀ x, TL ≤ V x)
    (ξ : EuclSpace d) :
    regV lam V ξ ≤ V ξ ∧ TL ≤ regV lam V ξ ∧ regV lam V ξ ≤ TU := by
  have hb := bddAbove_neg_of_bddBelow hVb
  have h1 := self_le_supConv hlam hb ξ
  have h2 := supConv_le_bound hlam (fun x => (by linarith [hTL x] : -V x ≤ -TL)) ξ
  unfold regV
  refine ⟨by linarith, by linarith, by linarith [hTU ξ]⟩

/-! ## Semiconvexity and continuity -/

theorem regU_semiconvex {lam : ℝ} (hlam : 0 ≤ lam) {U : EuclSpace d → ℝ}
    (hUb : BddAbove (range U)) : SemiconvexWith lam (regU lam U) :=
  semiconvex_supConv hlam hUb

theorem regV_semiconcave {lam : ℝ} (hlam : 0 ≤ lam) {V : EuclSpace d → ℝ}
    (hVb : BddBelow (range V)) : SemiconvexWith lam (fun y => -regV lam V y) := by
  rw [neg_regV]
  exact semiconvex_supConv hlam (bddAbove_neg_of_bddBelow hVb)

theorem regU_continuous {lam : ℝ} (hlam : 0 ≤ lam) {U : EuclSpace d → ℝ}
    (hUb : BddAbove (range U)) : Continuous (regU lam U) :=
  semiconvex_continuous (regU_semiconvex hlam hUb)

theorem regV_continuous {lam : ℝ} (hlam : 0 ≤ lam) {V : EuclSpace d → ℝ}
    (hVb : BddBelow (range V)) : Continuous (regV lam V) := by
  have h := semiconvex_continuous (regV_semiconcave hlam hVb)
  exact h.neg.congr fun y => neg_neg _

/-! ## Jets -/

theorem regU_jet (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p) {Ω : Set (EuclSpace d)}
    {U : EuclSpace d → ℝ} (hsub : IsViscositySubsolution p Ω (fun _ => 0) U)
    {lam : ℝ} (hlam : 0 < lam) (hU : UpperSemicontinuous U) (hUb : BddAbove (range U))
    {SU SL : ℝ} (hSU : ∀ x, U x ≤ SU) (hSL : ∀ x, SL ≤ U x)
    {ξ : EuclSpace d} {ρ : ℝ} (hρ : 2 * (SU - SL) / lam < ρ ^ 2) (hρ0 : 0 < ρ)
    (hball : ball ξ ρ ⊆ Ω) {q : EuclSpace d} {X : Bilin d}
    (hj : (q, X) ∈ SuperJet (regU lam U) ξ) (hq : q ≠ 0) : viscF p q X ≤ 0 :=
  supConv_jet hd hp hsub hlam hU hUb
    (supConv_maximizer_mem hlam hUb hSU hSL hρ hρ0 hball) hj hq

theorem regV_jet (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p) {Ω : Set (EuclSpace d)}
    {V : EuclSpace d → ℝ} (hsup : IsViscositySupersolution p Ω (fun _ => 0) V)
    {lam : ℝ} (hlam : 0 < lam) (hV : LowerSemicontinuous V) (hVb : BddBelow (range V))
    {TU TL : ℝ} (hTU : ∀ x, V x ≤ TU) (hTL : ∀ x, TL ≤ V x)
    {ξ : EuclSpace d} {ρ : ℝ} (hρ : 2 * (TU - TL) / lam < ρ ^ 2) (hρ0 : 0 < ρ)
    (hball : ball ξ ρ ⊆ Ω) {q : EuclSpace d} {X : Bilin d}
    (hj : (q, X) ∈ SuperJet (fun z => -regV lam V z) ξ) (hq : q ≠ 0) :
    viscF p q X ≤ 0 := by
  rw [neg_regV] at hj
  have hb := bddAbove_neg_of_bddBelow hVb
  have hρ' : 2 * (-TL - -TU) / lam < ρ ^ 2 := by
    rw [show -TL - -TU = TU - TL by ring]; exact hρ
  exact supConv_jet hd hp hsup.neg hlam (usc_neg_of_lsc hV) hb
    (supConv_maximizer_mem hlam hb (fun x => (by linarith [hTL x] : -V x ≤ -TL))
      (fun x => (by linarith [hTU x] : -TU ≤ -V x)) hρ' hρ0 hball) hj hq

end

end PLaplacian
