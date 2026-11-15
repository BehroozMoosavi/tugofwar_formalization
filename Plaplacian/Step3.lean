/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Step3M

@[expose] public section

/-! # The third step: no interior maximum above the boundary

With `W = V - η V²` and `K = {x ∈ G : U(x) - W(x) = M(0)}`:

1. `K` is nonempty: a maximizer at `h = 0` is interior.
2. At `x ∈ K`, `U` has a local maximum, since `U(x + h) - W(x) ≤ M(h) = M(0)`;
   and `V` a local minimum, since testing at `y = x - h` gives `W(y) ≥ W(x)`,
   and `ψ` is increasing.
3. The strong maximum principle, for `U` and for `-V`, makes both constant near
   `x`; so `K` is open.
4. `G \ K` is open by continuity; `G` is preconnected, so `K = G`.
5. `{U - W = M(0)}` is closed, so it contains `Ḡ`, and a frontier point — where
   the gap says `U - W < M(0)`.
-/

open Set Topology Filter Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



set_option maxHeartbeats 800000 in
-- The contact set, the two strong principles, and connectedness.
/-- **The third step.** -/
theorem step3 (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p) {U V : EuclSpace d → ℝ} {lam μ η Cc : ℝ}
    (hlam : 0 ≤ lam) (hμ : 0 ≤ μ) (hη : 0 < η)
    (hU : SemiconvexWith lam U) (hV : SemiconvexWith lam (fun y => -V y))
    (hW : SemiconvexWith μ (fun y => -(V y - η * V y ^ 2)))
    (hUc : Continuous U) (hVc : Continuous V)
    {O : Set (EuclSpace d)}
    (hUjet : ∀ y ∈ O, ∀ (q : EuclSpace d) (X : Bilin d), (q, X) ∈ SuperJet U y →
      q ≠ 0 → viscF p q X ≤ 0)
    (hVneg : ∀ y ∈ O, ∀ (q : EuclSpace d) (X : Bilin d),
      (q, X) ∈ SuperJet (fun z => -V z) y → q ≠ 0 → viscF p q X ≤ 0)
    (hc : ∀ y ∈ O, 0 < 1 - 2 * η * V y) (hCc : ∀ y ∈ O, 1 - 2 * η * V y ≤ Cc)
    {G : Set (EuclSpace d)} (hGo : IsOpen G) (hGb : Bornology.IsBounded G)
    (hne : G.Nonempty) (hGc : IsPreconnected G)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hGO : ∀ x ∈ closure G, ball x R₀ ⊆ O)
    {x₀ : EuclSpace d} (hx₀ : x₀ ∈ G)
    (hgap : ∀ z ∈ frontier G, U z - (V z - η * V z ^ 2) < U x₀ - (V x₀ - η * V x₀ ^ 2)) :
    False := by
  obtain ⟨h₁, hh₁, hconst, hint⟩ := Mfun_const hd hp hlam hμ hη hU hV hW hUc hVc hUjet hVneg
    hc hCc hGo hGb hne hR₀ hGO hx₀ hgap
  set M0 := Mfun U V η G 0 with hM0
  have hf0c : Continuous (fun z => U z - (V z - η * V z ^ 2)) := by fun_prop
  -- the bound by M(h), and its value
  have hleM : ∀ h, ‖h‖ < h₁ → ∀ x ∈ closure G, U (x + h) - (V x - η * V x ^ 2) ≤ M0 := by
    intro h hh x hx
    obtain ⟨_, _, _, hle⟩ := Mfun_attained (η := η) hUc hVc hGb hne h
    rw [← hconst h hh]
    exact hle x hx
  -- the contact set
  set K := {x | x ∈ G ∧ U x - (V x - η * V x ^ 2) = M0} with hKdef
  have hKne : (G ∩ K).Nonempty := by
    obtain ⟨xh, hxh, hxhM, _⟩ := Mfun_attained (η := η) hUc hVc hGb hne 0
    have hxhG : xh ∈ G := hint 0 (by rw [norm_zero]; exact hh₁) xh hxh hxhM
    rw [add_zero] at hxhM
    exact ⟨xh, hxhG, hxhG, hxhM⟩
  -- the semicontinuity needed by the strong principles
  have hUusc : UpperSemicontinuousOn U O := hUc.upperSemicontinuous.upperSemicontinuousOn O
  have hVusc : UpperSemicontinuousOn (fun z => -V z) O :=
    hVc.neg.upperSemicontinuous.upperSemicontinuousOn O
  -- K is open
  have hKo : IsOpen K := by
    rw [Metric.isOpen_iff]
    rintro x ⟨hxG, hxM⟩
    obtain ⟨ρ₁, hρ₁, hρ₁G⟩ := Metric.isOpen_iff.1 hGo x hxG
    set R := min h₁ (min ρ₁ R₀) with hR
    have hR0 : 0 < R := lt_min hh₁ (lt_min hρ₁ hR₀)
    have hRG : ball x R ⊆ G :=
      fun y hy => hρ₁G (ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _)) hy)
    have hRO : ball x R ⊆ O := fun y hy =>
      hGO x (subset_closure hxG)
        (ball_subset_ball (le_trans (min_le_right _ _) (min_le_right _ _)) hy)
    have hRh : ∀ y ∈ ball x R, ‖y - x‖ < h₁ := by
      intro y hy
      rw [mem_ball, dist_eq_norm] at hy
      exact lt_of_lt_of_le hy (min_le_left _ _)
    -- U has a local maximum at x
    have hUmax : ∀ y ∈ ball x R, U y ≤ U x := by
      intro y hy
      have h1 := hleM (y - x) (hRh y hy) x (subset_closure hxG)
      have e : x + (y - x) = y := by abel
      rw [e] at h1
      linarith
    -- V has a local minimum at x
    have hVmin : ∀ y ∈ ball x R, -V y ≤ -V x := by
      intro y hy
      have hy' : ‖x - y‖ < h₁ := by rw [norm_sub_rev]; exact hRh y hy
      have h1 := hleM (x - y) hy' y (subset_closure (hRG hy))
      have e : y + (x - y) = x := by abel
      rw [e] at h1
      have hW : V x - η * V x ^ 2 ≤ V y - η * V y ^ 2 := by linarith
      have := psi_mono (hc x (hRO (mem_ball_self hR0))) (hc y (hRO hy)) hW
      linarith
    have hUconst := smp_ball_jet hd hp hUusc hUjet hR0 hRO hUmax
    have hVconst := smp_ball_jet hd hp hVusc hVneg hR0 hRO hVmin
    refine ⟨R / 3, by positivity, fun y hy => ⟨hRG (ball_subset_ball (by linarith) hy), ?_⟩⟩
    have h1 := hUconst y hy
    have h2 : V y = V x := by have := hVconst y hy; linarith
    rw [h1, h2]
    exact hxM
  -- the complement in G is open
  have hSo : IsOpen {x | U x - (V x - η * V x ^ 2) ≠ M0} :=
    isOpen_ne_fun hf0c continuous_const
  have hdisj : Disjoint K {x | U x - (V x - η * V x ^ 2) ≠ M0} :=
    Set.disjoint_left.2 fun x hxK hxS => hxS hxK.2
  have hcover : G ⊆ K ∪ {x | U x - (V x - η * V x ^ 2) ≠ M0} := by
    intro x hx
    by_cases h : U x - (V x - η * V x ^ 2) = M0
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h
  -- connectedness
  have hGK : G ⊆ K :=
    IsPreconnected.subset_left_of_subset_union hKo hSo hdisj hcover hKne hGc
  have hclosed : closure G ⊆ {x | U x - (V x - η * V x ^ 2) = M0} := by
    apply closure_minimal _ (isClosed_eq hf0c continuous_const)
    intro x hx
    exact (hGK hx).2
  -- the contradiction at a frontier point
  obtain ⟨z, hz⟩ := frontier_nonempty hd hGo hGb hne
  have h1 : U z - (V z - η * V z ^ 2) = M0 := hclosed (frontier_subset_closure hz)
  have h2 := hleM 0 (by rw [norm_zero]; exact hh₁) x₀ (subset_closure hx₀)
  rw [add_zero] at h2
  have h3 := hgap z hz
  linarith

end

end PLaplacian
