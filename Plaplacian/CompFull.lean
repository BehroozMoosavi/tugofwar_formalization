/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.BandEst

/-! # The comparison principle

A bounded upper semicontinuous viscosity subsolution and a bounded lower
semicontinuous viscosity supersolution of `-Δᴺₚ u = 0` on a bounded open set,
ordered on the boundary, are ordered inside.

The argument is J. J. Manfredi's. Suppose `θ = U(x̄) - V(x̄) > 0`.

1. `δ` comes from the band estimate with `θ/4` and is at most
   `dist(x̄, Ωᶜ)/2`; `λ` is large for the band estimate and for the jets on
   `O = {dist(·, Ωᶜ) > δ/2}`; `η` is small, so `1/2 ≤ 1 - 2ηV_λ ≤ 3/2` and
   `ηV_λ² ≤ θ/8`.
2. `f = U_λ - (V_λ - ηV_λ²)` has `f(x̄) ≥ θ`, and `f < θ/2` on the band.
3. `G` is the component of `S = {dist(·, Ωᶜ) > δ} ∩ {f > θ/2}` containing `x̄`.
   A frontier point of `G` lies outside `S` — otherwise a small ball about it
   would lie in `S` and meet `G`, putting it inside the open set `G` — so
   `f ≤ θ/2` there, directly or by the band estimate.
4. The third step applies, with the gap `f(z) ≤ θ/2 < θ ≤ f(x̄)`.
-/

open Set Topology Filter Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



set_option maxHeartbeats 1600000 in
-- The parameters, the component, and the third step.
/-- **The comparison principle** for the homogeneous normalized `p`-Laplacian. -/
theorem visc_comparison (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p) {Ω : Set (EuclSpace d)}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) {U V : EuclSpace d → ℝ}
    (hU : UpperSemicontinuous U) (hV : LowerSemicontinuous V)
    (hUb : BddAbove (range U)) (hUb' : BddBelow (range U))
    (hVb : BddBelow (range V)) (hVb' : BddAbove (range V))
    (hsub : IsViscositySubsolution p Ω (fun _ => 0) U)
    (hsup : IsViscositySupersolution p Ω (fun _ => 0) V)
    (hbd : ∀ x ∈ frontier Ω, U x ≤ V x) :
    ∀ x ∈ Ω, U x ≤ V x := by
  intro xb hxb
  by_contra hlt
  push Not at hlt
  set θ := U xb - V xb with hθdef
  have hθ : 0 < θ := by linarith
  -- the bounds
  obtain ⟨SU, hSU'⟩ := hUb
  obtain ⟨SL, hSL'⟩ := hUb'
  obtain ⟨TL, hTL'⟩ := hVb
  obtain ⟨TU, hTU'⟩ := hVb'
  have hSU : ∀ x, U x ≤ SU := fun x => hSU' ⟨x, rfl⟩
  have hSL : ∀ x, SL ≤ U x := fun x => hSL' ⟨x, rfl⟩
  have hTL : ∀ x, TL ≤ V x := fun x => hTL' ⟨x, rfl⟩
  have hTU : ∀ x, V x ≤ TU := fun x => hTU' ⟨x, rfl⟩
  have hUbA : BddAbove (range U) := ⟨SU, hSU'⟩
  have hVbB : BddBelow (range V) := ⟨TL, hTL'⟩
  have hCU : 0 ≤ SU - SL := by linarith [hSU 0, hSL 0]
  have hCV : 0 ≤ TU - TL := by linarith [hTU 0, hTL 0]
  -- the complement, and the distance of x̄ to it
  have hΩc := compl_nonempty hd hΩb
  have hxbd : 0 < infDist xb Ωᶜ :=
    (hΩo.isClosed_compl.notMem_iff_infDist_pos hΩc).1 (fun h => h hxb)
  -- δ from the band estimate
  obtain ⟨δ₀, hδ₀, Λ, hΛ, hband⟩ := band_est hΩb hΩc hU hV hUbA hVbB hSU hSL hTU hTL hbd
    (θ := θ / 4) (by positivity)
  set δ := min δ₀ (infDist xb Ωᶜ / 2) with hδdef
  have hδ : 0 < δ := lt_min hδ₀ (by positivity)
  have hδδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδxb : δ < infDist xb Ωᶜ := by
    have : δ ≤ infDist xb Ωᶜ / 2 := min_le_right _ _
    linarith
  -- λ
  set C := (SU - SL) + (TU - TL) + 1 with hC
  have hC0 : 0 < C := by linarith
  set lam := Λ + 8 * C / δ ^ 2 + 1 with hlamdef
  have hlamC : 8 * C / δ ^ 2 ≤ lam := by
    have : 0 < Λ := hΛ
    linarith
  have hlam0 : 0 < lam := lt_of_lt_of_le (by positivity) hlamC
  have hlamΛ : Λ ≤ lam := by
    have : 0 ≤ 8 * C / δ ^ 2 := by positivity
    linarith
  have hρ2 : 2 * C < (δ / 2) ^ 2 * lam + 1 := by
    have h1 : (δ / 2) ^ 2 * (8 * C / δ ^ 2) = 2 * C := by field_simp; ring
    have h2 := mul_le_mul_of_nonneg_left hlamC (by positivity : (0 : ℝ) ≤ (δ / 2) ^ 2)
    linarith
  have hρU : 2 * (SU - SL) / lam < (δ / 2) ^ 2 := by
    rw [div_lt_iff₀ hlam0]
    have h1 : (δ / 2) ^ 2 * (8 * C / δ ^ 2) = 2 * C := by field_simp; ring
    have h2 := mul_le_mul_of_nonneg_left hlamC (by positivity : (0 : ℝ) ≤ (δ / 2) ^ 2)
    nlinarith
  have hρV : 2 * (TU - TL) / lam < (δ / 2) ^ 2 := by
    rw [div_lt_iff₀ hlam0]
    have h1 : (δ / 2) ^ 2 * (8 * C / δ ^ 2) = 2 * C := by field_simp; ring
    have h2 := mul_le_mul_of_nonneg_left hlamC (by positivity : (0 : ℝ) ≤ (δ / 2) ^ 2)
    nlinarith
  -- the bounds on V_λ, and η
  have hVlam := regV_bounds hlam0.le hVbB hTU hTL
  set B := |TL| + |TU| + 1 with hB
  have hB0 : 0 < B := by positivity
  have hVB : ∀ y, |regV lam V y| ≤ B := by
    intro y
    obtain ⟨_, h1, h2⟩ := hVlam y
    rw [abs_le]
    constructor
    · have := neg_abs_le TL; linarith [abs_nonneg TU]
    · have := le_abs_self TU; linarith [abs_nonneg TL]
  set η := min (1 / (4 * B)) (θ / (8 * B ^ 2)) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηB : η * B ≤ 1 / 4 := by
    have := mul_le_mul_of_nonneg_right (min_le_left (1 / (4 * B)) (θ / (8 * B ^ 2))) hB0.le
    have e : 1 / (4 * B) * B = 1 / 4 := by field_simp
    linarith
  have hηB2 : η * B ^ 2 ≤ θ / 8 := by
    have := mul_le_mul_of_nonneg_right (min_le_right (1 / (4 * B)) (θ / (8 * B ^ 2)))
      (by positivity : (0 : ℝ) ≤ B ^ 2)
    have e : θ / (8 * B ^ 2) * B ^ 2 = θ / 8 := by field_simp
    linarith
  have hcb : ∀ y, 1 / 2 ≤ 1 - 2 * η * regV lam V y ∧ 1 - 2 * η * regV lam V y ≤ 3 / 2 := by
    intro y
    obtain ⟨a1, a2⟩ := abs_le.1 (hVB y)
    have k1 : η * regV lam V y ≤ η * B := mul_le_mul_of_nonneg_left a2 hη.le
    have k2 : η * (-B) ≤ η * regV lam V y := mul_le_mul_of_nonneg_left a1 hη.le
    constructor <;> nlinarith
  have hsq : ∀ y, η * regV lam V y ^ 2 ≤ θ / 8 := by
    intro y
    have h1 : regV lam V y ^ 2 ≤ B ^ 2 := by
      have := hVB y
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    have := mul_le_mul_of_nonneg_left h1 hη.le
    linarith
  -- the function f, at x̄ and on the band
  have hUc := regU_continuous hlam0.le hUbA
  have hVc := regV_continuous hlam0.le hVbB
  have hfc : Continuous (fun z => regU lam U z - (regV lam V z - η * regV lam V z ^ 2)) := by
    fun_prop
  have hfx : θ ≤ regU lam U xb - (regV lam V xb - η * regV lam V xb ^ 2) := by
    have h1 := (regU_bounds hlam0.le hUbA hSU hSL xb).1
    have h2 := (hVlam xb).1
    have h3 : 0 ≤ η * regV lam V xb ^ 2 := by positivity
    linarith
  have hfband : ∀ x ∈ closure Ω, infDist x Ωᶜ ≤ 2 * δ →
      regU lam U x - (regV lam V x - η * regV lam V x ^ 2) < θ / 2 := by
    intro x hx hxd
    have h1 := hband lam hlamΛ x hx (le_trans hxd (by linarith))
    have h2 := hsq x
    linarith
  -- the set S and the component G
  set S := {x | δ < infDist x Ωᶜ} ∩
    {x | θ / 2 < regU lam U x - (regV lam V x - η * regV lam V x ^ 2)} with hSdef
  have hSo : IsOpen S :=
    (isOpen_lt continuous_const (continuous_infDist_pt _)).inter
      (isOpen_lt continuous_const hfc)
  have hxbS : xb ∈ S := ⟨hδxb, by change θ / 2 < _; linarith⟩
  have hSΩ : S ⊆ Ω := by
    intro x hx
    by_contra hxΩ
    have : infDist x Ωᶜ = 0 := infDist_zero_of_mem hxΩ
    have h1 : δ < infDist x Ωᶜ := hx.1
    linarith
  set G := connectedComponentIn S xb with hGdef
  have hGo : IsOpen G := hSo.connectedComponentIn
  have hGc : IsPreconnected G := isPreconnected_connectedComponentIn
  have hxbG : xb ∈ G := mem_connectedComponentIn hxbS
  have hGne : G.Nonempty := ⟨xb, hxbG⟩
  have hGS : G ⊆ S := connectedComponentIn_subset S xb
  have hGb : Bornology.IsBounded G := hΩb.subset (hGS.trans hSΩ)
  have hclG : closure G ⊆ {x | δ ≤ infDist x Ωᶜ} := by
    apply closure_minimal _ (isClosed_le continuous_const (continuous_infDist_pt _))
    intro x hx
    have h : δ < infDist x Ωᶜ := (hGS hx).1
    exact h.le
  have hclGΩ : closure G ⊆ closure Ω := closure_mono (hGS.trans hSΩ)
  -- the frontier of G lies where f ≤ θ/2
  have hfr : ∀ z ∈ frontier G,
      regU lam U z - (regV lam V z - η * regV lam V z ^ 2) ≤ θ / 2 := by
    intro z hz
    by_contra hgt
    push Not at hgt
    have hzcl : z ∈ closure G := frontier_subset_closure hz
    rcases lt_or_ge δ (infDist z Ωᶜ) with hzd | hzd
    · -- z ∈ S would put z inside G
      have hzS : z ∈ S := ⟨hzd, hgt⟩
      obtain ⟨r, hr, hrS⟩ := Metric.isOpen_iff.1 hSo z hzS
      obtain ⟨w, hwG, hwz⟩ := Metric.mem_closure_iff.1 hzcl r hr
      have hwball : w ∈ ball z r := by rw [mem_ball, dist_comm]; exact hwz
      have hGw : G = connectedComponentIn S w := connectedComponentIn_eq hwG
      have hball : ball z r ⊆ connectedComponentIn S w :=
        (convex_ball z r).isPreconnected.subset_connectedComponentIn hwball hrS
      have hzG : z ∈ G := by rw [hGw]; exact hball (mem_ball_self hr)
      have hzint : z ∉ interior G := hz.2
      rw [hGo.interior_eq] at hzint
      exact hzint hzG
    · -- z lies in the band
      have h1 := hfband z (hclGΩ hzcl) (by linarith)
      linarith
  have hgap : ∀ z ∈ frontier G,
      regU lam U z - (regV lam V z - η * regV lam V z ^ 2)
        < regU lam U xb - (regV lam V xb - η * regV lam V xb ^ 2) := by
    intro z hz
    have := hfr z hz
    linarith
  -- the region O where the jet inequalities hold
  set O := {x | δ / 2 < infDist x Ωᶜ} with hOdef
  have hOball : ∀ y ∈ O, ball y (δ / 2) ⊆ Ω := by
    intro y hy w hw
    by_contra hwΩ
    have h1 := infDist_le_dist_of_mem (x := y) (show w ∈ Ωᶜ from hwΩ)
    have h2 : δ / 2 < infDist y Ωᶜ := hy
    rw [mem_ball, dist_comm] at hw
    linarith
  have hUjet : ∀ y ∈ O, ∀ (q : EuclSpace d) (X : Bilin d),
      (q, X) ∈ SuperJet (regU lam U) y → q ≠ 0 → viscF p q X ≤ 0 :=
    fun y hy q X hj hq => regU_jet hd hp hsub hlam0 hU hUbA hSU hSL hρU (by positivity)
      (hOball y hy) hj hq
  have hVneg : ∀ y ∈ O, ∀ (q : EuclSpace d) (X : Bilin d),
      (q, X) ∈ SuperJet (fun z => -regV lam V z) y → q ≠ 0 → viscF p q X ≤ 0 :=
    fun y hy q X hj hq => regV_jet hd hp hsup hlam0 hV hVbB hTU hTL hρV (by positivity)
      (hOball y hy) hj hq
  have hGO : ∀ x ∈ closure G, ball x (δ / 2) ⊆ O := by
    intro x hx y hy
    have h1 : δ ≤ infDist x Ωᶜ := hclG hx
    have h2 := infDist_le_infDist_add_dist (s := Ωᶜ) (x := x) (y := y)
    rw [mem_ball, dist_comm] at hy
    change δ / 2 < infDist y Ωᶜ
    linarith
  -- semiconvexity
  have hUs := regU_semiconvex hlam0.le hUbA
  have hVs := regV_semiconcave hlam0.le hVbB
  have hWs := semiconcave_psi (Cc := 3 / 2) hlam0.le hη.le hVs
    (fun y => by linarith [(hcb y).1]) (fun y => (hcb y).2)
  -- the third step
  exact step3 hd hp hlam0.le (by positivity) hη hUs hVs hWs hUc hVc hUjet hVneg
    (fun y _ => by linarith [(hcb y).1]) (fun y _ => (hcb y).2)
    hGo hGb hGne hGc (by positivity : (0 : ℝ) < δ / 2) hGO hxbG hgap

end

end PLaplacian
