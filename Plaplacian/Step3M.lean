/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Step3Tools

@[expose] public section

/-! # The translated maximum is constant

With `W = V - η V²`, `f_h(x) = U(x + h) - W(x)` and `M(h) = sup_{Ḡ} f_h`:

1. `Ḡ` is compact, so `M(h)` is attained and bounds `f_h` on `Ḡ`.
2. The gap on `∂G` is a definite `γ > 0`, by compactness of the frontier, and
   `U` is uniformly continuous on `Ḡ + B̄(0, 1)`; so for `|h| < h₀` a maximizer
   on the frontier would give `M(h) < f_h(x₀)`. Maximizers are interior.
3. At an interior maximizer `x_h`, the second step applies to `U(· + h)` on a
   small ball: its lower support is zero, so
   `M(h + k) ≥ f_{h+k}(x_h) ≥ M(h) - (λ/2)|k|²`.
4. By subdivision, `M(h) = M(0)` for small `h`.
-/

open Set Topology Filter Metric
open scoped Pointwise

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- **The translated maximum.** -/
def Mfun (U V : EuclSpace d → ℝ) (η : ℝ) (G : Set (EuclSpace d)) (h : EuclSpace d) : ℝ :=
  sSup ((fun x => U (x + h) - (V x - η * V x ^ 2)) '' closure G)

section M

variable {U V : EuclSpace d → ℝ} {η : ℝ} {G : Set (EuclSpace d)}

/-- **The translated maximum is attained.** -/
theorem Mfun_attained (hUc : Continuous U) (hVc : Continuous V)
    (hGb : Bornology.IsBounded G) (hne : G.Nonempty) (h : EuclSpace d) :
    ∃ xh ∈ closure G, U (xh + h) - (V xh - η * V xh ^ 2) = Mfun U V η G h ∧
      ∀ x ∈ closure G, U (x + h) - (V x - η * V x ^ 2) ≤ Mfun U V η G h := by
  have hK : IsCompact (closure G) := hGb.isCompact_closure
  have hcont : Continuous (fun x => U (x + h) - (V x - η * V x ^ 2)) := by fun_prop
  obtain ⟨xh, hxh, hmax⟩ := hK.exists_isMaxOn (hne.mono subset_closure) hcont.continuousOn
  have hle : ∀ x ∈ closure G, U (x + h) - (V x - η * V x ^ 2)
      ≤ U (xh + h) - (V xh - η * V xh ^ 2) := fun x hx => hmax hx
  have hbdd : BddAbove ((fun x => U (x + h) - (V x - η * V x ^ 2)) '' closure G) := by
    refine ⟨U (xh + h) - (V xh - η * V xh ^ 2), ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact hle x hx
  have hM : Mfun U V η G h = U (xh + h) - (V xh - η * V xh ^ 2) := by
    unfold Mfun
    refine le_antisymm (csSup_le ((hne.mono subset_closure).image _) ?_)
      (le_csSup hbdd ⟨xh, hxh, rfl⟩)
    rintro _ ⟨x, hx, rfl⟩
    exact hle x hx
  refine ⟨xh, hxh, hM.symm, fun x hx => ?_⟩
  rw [hM]
  exact hle x hx

/-- **Maximizers are interior for small translations.** -/
theorem Mfun_interior (hUc : Continuous U) (hVc : Continuous V) (hGo : IsOpen G)
    (hGb : Bornology.IsBounded G) (hne : G.Nonempty) {x₀ : EuclSpace d} (hx₀ : x₀ ∈ G)
    (hgap : ∀ z ∈ frontier G, U z - (V z - η * V z ^ 2) < U x₀ - (V x₀ - η * V x₀ ^ 2)) :
    ∃ h₀ > 0, ∀ h, ‖h‖ < h₀ → ∀ x ∈ closure G,
      U (x + h) - (V x - η * V x ^ 2) = Mfun U V η G h → x ∈ G := by
  have hK : IsCompact (closure G) := hGb.isCompact_closure
  have hf0 : Continuous (fun z => U z - (V z - η * V z ^ 2)) := by fun_prop
  -- a definite gap on the frontier
  obtain ⟨γ, hγ, hgapγ⟩ : ∃ γ > 0, ∀ z ∈ frontier G,
      U z - (V z - η * V z ^ 2) ≤ U x₀ - (V x₀ - η * V x₀ ^ 2) - γ := by
    by_cases hfr : (frontier G).Nonempty
    · have hFc : IsCompact (frontier G) :=
        hK.of_isClosed_subset isClosed_frontier frontier_subset_closure
      obtain ⟨z₀, hz₀, hzmax⟩ := hFc.exists_isMaxOn hfr hf0.continuousOn
      have h1 := hgap z₀ hz₀
      refine ⟨U x₀ - (V x₀ - η * V x₀ ^ 2) - (U z₀ - (V z₀ - η * V z₀ ^ 2)), by linarith,
        fun z hz => ?_⟩
      have : U z - (V z - η * V z ^ 2) ≤ U z₀ - (V z₀ - η * V z₀ ^ 2) := hzmax hz
      linarith
    · refine ⟨1, one_pos, fun z hz => absurd ⟨z, hz⟩ hfr⟩
  -- uniform continuity of U near Ḡ
  have hKt : IsCompact (closure G + closedBall (0 : EuclSpace d) 1) :=
    hK.add (isCompact_closedBall 0 1)
  have hUu := hKt.uniformContinuousOn_of_continuous hUc.continuousOn
  obtain ⟨δ₁, hδ₁, hu⟩ := Metric.uniformContinuousOn_iff.1 hUu (γ / 2) (by positivity)
  have hclose : ∀ h : EuclSpace d, ‖h‖ < min 1 δ₁ → ∀ y ∈ closure G,
      |U (y + h) - U y| < γ / 2 := by
    intro h hh y hy
    have h1 : y + h ∈ closure G + closedBall (0 : EuclSpace d) 1 :=
      add_mem_add hy (mem_closedBall_zero_iff.2 (le_trans hh.le (min_le_left _ _)))
    have h2 : y ∈ closure G + closedBall (0 : EuclSpace d) 1 := by
      have := add_mem_add hy (mem_closedBall_self (x := (0 : EuclSpace d)) zero_le_one)
      rwa [add_zero] at this
    have h3 : dist (y + h) y < δ₁ := by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact lt_of_lt_of_le hh (min_le_right _ _)
    have := hu _ h1 _ h2 h3
    rwa [Real.dist_eq] at this
  refine ⟨min 1 δ₁, lt_min one_pos hδ₁, fun h hh x hx hxM => ?_⟩
  by_contra hxG
  have hxF : x ∈ frontier G := ⟨hx, by rw [hGo.interior_eq]; exact hxG⟩
  have h1 := hgapγ x hxF
  have h2 := hclose h hh x hx
  have h3 := hclose h hh x₀ (subset_closure hx₀)
  obtain ⟨_, _, _, hle⟩ := Mfun_attained (η := η) hUc hVc hGb hne h
  have h4 := hle x₀ (subset_closure hx₀)
  obtain ⟨a1, a2⟩ := abs_le.1 h2.le
  obtain ⟨b1, b2⟩ := abs_lt.1 h3
  obtain ⟨c1, c2⟩ := abs_lt.1 h2
  linarith

end M

/-! ## The lower bound, and constancy -/

section const

variable {U V : EuclSpace d → ℝ} {η : ℝ} {G : Set (EuclSpace d)}

set_option maxHeartbeats 800000 in
-- The second step, applied to a translate on a small ball.
/-- **`M(h + k) ≥ M(h) - (λ/2)|k|²` for small `h`.** -/
theorem Mfun_lower (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p) {lam μ Cc : ℝ}
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
    (hGo : IsOpen G) (hGb : Bornology.IsBounded G) (hne : G.Nonempty)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hGO : ∀ x ∈ closure G, ball x R₀ ⊆ O)
    {h : EuclSpace d} (hh : ‖h‖ < R₀ / 2)
    (hint : ∀ x ∈ closure G, U (x + h) - (V x - η * V x ^ 2) = Mfun U V η G h → x ∈ G) :
    ∀ k, Mfun U V η G h - lam / 2 * ‖k‖ ^ 2 ≤ Mfun U V η G (h + k) := by
  obtain ⟨xh, hxh, hxhM, hle⟩ := Mfun_attained (η := η) hUc hVc hGb hne h
  have hxhG : xh ∈ G := hint xh hxh hxhM
  obtain ⟨ρ₁, hρ₁, hρ₁G⟩ := Metric.isOpen_iff.1 hGo xh hxhG
  set ρ := min ρ₁ (R₀ / 2) with hρ
  have hρ0 : 0 < ρ := lt_min hρ₁ (by positivity)
  -- the ball around xh: inside G, and inside O together with its translate
  have hballG : ball xh ρ ⊆ G := fun y hy => hρ₁G (ball_subset_ball (min_le_left _ _) hy)
  have hO1 : ∀ y ∈ ball xh ρ, y ∈ O := fun y hy =>
    hGO xh hxh (ball_subset_ball (by linarith [min_le_right ρ₁ (R₀ / 2)]) hy)
  have hO2 : ∀ y ∈ ball xh ρ, y + h ∈ O := by
    intro y hy
    apply hGO xh hxh
    rw [mem_ball] at hy ⊢
    calc dist (y + h) xh ≤ dist y xh + dist (y + h) y := by
          have := dist_triangle (y + h) y xh
          linarith
      _ = dist y xh + ‖h‖ := by rw [dist_eq_norm (y + h) y, add_sub_cancel_left]
      _ < R₀ / 2 + R₀ / 2 := by
          have : ρ ≤ R₀ / 2 := min_le_right _ _
          linarith
      _ = R₀ := by ring
  -- the hypotheses of the second step for U(· + h)
  have hUjet' : ∀ y ∈ ball xh ρ, ∀ (q : EuclSpace d) (X : Bilin d),
      (q, X) ∈ SuperJet (fun z => U (z + h)) y → q ≠ 0 → viscF p q X ≤ 0 :=
    fun y hy q X hj hq => hUjet (y + h) (hO2 y hy) q X (superJet_translate hj) hq
  have hVjetO := subJet_ineq_of_neg hVneg
  have hVjet' : ∀ y ∈ ball xh ρ, ∀ (q : EuclSpace d) (X : Bilin d),
      (q, X) ∈ SubJet V y → q ≠ 0 → 0 ≤ viscF p q X :=
    fun y hy => hVjetO y (hO1 y hy)
  have hc' : ∀ y ∈ ball xh ρ, 0 < 1 - 2 * η * V y := fun y hy => hc y (hO1 y hy)
  have hCc' : ∀ y ∈ ball xh ρ, 1 - 2 * η * V y ≤ Cc := fun y hy => hCc y (hO1 y hy)
  have hmax' : ∀ y ∈ ball xh ρ, U (y + h) - (V y - η * V y ^ 2)
      ≤ U (xh + h) - (V xh - η * V xh ^ 2) := by
    intro y hy
    rw [hxhM]
    exact hle y (subset_closure (hballG hy))
  -- the lower support of U(· + h) at xh is zero
  obtain ⟨q, hq⟩ := semiconvex_support (semiconvex_translate hU h) xh
  have hq' : ∀ y, U (xh + h) + inner ℝ q (y - xh) - lam / 2 * ‖y - xh‖ ^ 2 ≤ U (y + h) := hq
  have hq0 : q = 0 := step2 hd hp hlam hμ hη (semiconvex_translate hU h) hV hW
    hUjet' hVjet' hc' hCc' hρ0 (subset_refl _) hmax' hq'
  -- the lower bound
  intro k
  have h1 := hq' (xh + k)
  rw [hq0, inner_zero_left, add_zero] at h1
  have e1 : xh + k - xh = k := by abel
  rw [e1] at h1
  obtain ⟨_, _, _, hle'⟩ := Mfun_attained (η := η) hUc hVc hGb hne (h + k)
  have h2 := hle' xh hxh
  have e2 : xh + (h + k) = xh + k + h := by abel
  rw [e2] at h2
  rw [← hxhM]
  linarith

set_option maxHeartbeats 800000 in
-- Combining the interior lemma, the lower bound, and subdivision.
/-- **The translated maximum is constant near `0`.** -/
theorem Mfun_const (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p) {lam μ Cc : ℝ}
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
    (hGo : IsOpen G) (hGb : Bornology.IsBounded G) (hne : G.Nonempty)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hGO : ∀ x ∈ closure G, ball x R₀ ⊆ O)
    {x₀ : EuclSpace d} (hx₀ : x₀ ∈ G)
    (hgap : ∀ z ∈ frontier G, U z - (V z - η * V z ^ 2) < U x₀ - (V x₀ - η * V x₀ ^ 2)) :
    ∃ h₁ > 0, (∀ h, ‖h‖ < h₁ → Mfun U V η G h = Mfun U V η G 0) ∧
      (∀ h, ‖h‖ < h₁ → ∀ x ∈ closure G,
        U (x + h) - (V x - η * V x ^ 2) = Mfun U V η G h → x ∈ G) := by
  obtain ⟨h₀, hh₀, hint⟩ := Mfun_interior (η := η) hUc hVc hGo hGb hne hx₀ hgap
  set h₁ := min h₀ (R₀ / 2) with hh₁def
  have hh₁ : 0 < h₁ := lt_min hh₀ (by positivity)
  have hint' : ∀ h, ‖h‖ < h₁ → ∀ x ∈ closure G,
      U (x + h) - (V x - η * V x ^ 2) = Mfun U V η G h → x ∈ G :=
    fun h hh => hint h (lt_of_lt_of_le hh (min_le_left _ _))
  have hlow : ∀ h ∈ ball (0 : EuclSpace d) h₁, ∀ k,
      Mfun U V η G h - lam / 2 * ‖k‖ ^ 2 ≤ Mfun U V η G (h + k) := by
    intro h hh
    rw [mem_ball_zero_iff] at hh
    exact Mfun_lower hd hp hlam hμ hη hU hV hW hUc hVc hUjet hVneg hc hCc hGo hGb hne hR₀ hGO
      (lt_of_lt_of_le hh (min_le_right _ _)) (hint' h hh)
  have hC : 0 ≤ lam / 2 := by positivity
  have hmono := const_of_quad_lower (g := Mfun U V η G) hC hlow
  refine ⟨h₁, hh₁, fun h hh => ?_, hint'⟩
  have h0 : (0 : EuclSpace d) ∈ ball (0 : EuclSpace d) h₁ := mem_ball_self hh₁
  have hb : h ∈ ball (0 : EuclSpace d) h₁ := mem_ball_zero_iff.2 hh
  exact le_antisymm (hmono h hb 0 h0) (hmono 0 h0 h hb)

end const

end

end PLaplacian
