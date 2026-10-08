/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.SMPBarrier

/-! # The strong maximum principle

A subsolution of `-Δᴺₚ u = 0` with an interior maximum is constant near it: if
`u ≤ u(x)` on `B(x, R) ⊆ Ω`, then `u ≡ u(x)` on `B(x, R/3)`.

Suppose `u(y₀) < m = u(x)` with `y₀ ∈ B(x, R/3)`.

1. The contact set `S = B̄(y₀, R/2) ∩ {u ≥ m}` is compact, by upper
   semicontinuity, and contains `x`.
2. With `r = dist(y₀, S) > 0` and `z ∈ S` nearest, `u < m` on `B(y₀, r)` and
   `u(z) = m`.
3. With `κ = (p - 1)/(12(d + p - 2)) ≤ 1/12`, `θ = κ r`, `B = r² + κ r²`, the
   maximum of `u` on `B̄(y₀, r - θ)` is `m - δ`, and `ε = δ/(2(9κ²r⁴ + 1))`.
4. A maximizer `w` of `g = u + ε φ` on the annulus `r - θ ≤ |y - y₀| ≤ r`,
   `φ` the barrier, is not on the inner sphere, where `g ≤ m - δ/2 < g(z)`, and is
   a genuine local maximum: just outside the annulus `φ < φ(z)` and `u ≤ m`.
5. The superjet at `w` gives `viscF ≤ 0`, but `viscF = ε[8(p-1)s - 4(B-s)(d+p-2)]`
   is at least `ε(p - 1)r² > 0`.

The arithmetic is in three lemmas with small contexts, so that `nlinarith` stays
fast.
-/

open Set Topology Filter Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-! ## The arithmetic -/

/-- **The barrier on the annulus.** -/
theorem barrier_annulus_bound {t r κ : ℝ} (hr : 0 < r) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1 / 12)
    (h1 : r - κ * r ≤ t) (h2 : t ≤ r) :
    (t ^ 2 - (r ^ 2 + κ * r ^ 2)) ^ 2 ≤ 9 * κ ^ 2 * r ^ 4 := by
  have hκr : κ * r ≤ r / 12 := by
    have := mul_le_mul_of_nonneg_right hκ1 hr.le
    linarith
  have h0 : 0 ≤ r - κ * r := by linarith
  have hlo : (r - κ * r) ^ 2 ≤ t ^ 2 := by
    rw [sq, sq]; exact mul_self_le_mul_self h0 h1
  have hhi : t ^ 2 ≤ r ^ 2 := by
    rw [sq, sq]; exact mul_self_le_mul_self (by linarith) h2
  have hk2 : 0 ≤ κ ^ 2 * r ^ 2 := by positivity
  have hk1 : 0 ≤ κ * r ^ 2 := by positivity
  have e0 : (r - κ * r) ^ 2 = r ^ 2 - 2 * (κ * r ^ 2) + κ ^ 2 * r ^ 2 := by ring
  have e1 : -(3 * κ * r ^ 2) ≤ t ^ 2 - (r ^ 2 + κ * r ^ 2) := by linarith
  have e2 : t ^ 2 - (r ^ 2 + κ * r ^ 2) ≤ 3 * κ * r ^ 2 := by linarith
  calc (t ^ 2 - (r ^ 2 + κ * r ^ 2)) ^ 2 ≤ (3 * κ * r ^ 2) ^ 2 := sq_le_sq' e1 e2
    _ = 9 * κ ^ 2 * r ^ 4 := by ring

/-- **The barrier just outside the annulus.** -/
theorem barrier_outside_bound {t r κ : ℝ} (hr : 0 < r) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1 / 12)
    (h1 : r < t) (h2 : t < r + κ * r / 2) :
    (t ^ 2 - (r ^ 2 + κ * r ^ 2)) ^ 2 ≤ (κ * r ^ 2) ^ 2 := by
  have hlo : r ^ 2 < t ^ 2 := by nlinarith
  have hhi : t ^ 2 < (r + κ * r / 2) ^ 2 := by nlinarith
  have e0 : (r + κ * r / 2) ^ 2 = r ^ 2 + κ * r ^ 2 + κ ^ 2 * r ^ 2 / 4 := by ring
  have hk : κ ^ 2 * r ^ 2 ≤ κ * r ^ 2 := by
    have : κ ^ 2 ≤ κ := by nlinarith
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have hk1 : 0 ≤ κ * r ^ 2 := by positivity
  have e1 : -(κ * r ^ 2) ≤ t ^ 2 - (r ^ 2 + κ * r ^ 2) := by linarith
  have e2 : t ^ 2 - (r ^ 2 + κ * r ^ 2) ≤ κ * r ^ 2 := by linarith
  exact sq_le_sq' e1 e2

/-- **The operator's value at the maximizer is positive.** -/
theorem smp_value_pos {p D r κ s : ℝ} (hp : 2 ≤ p) (hD : 0 < D) (hr : 0 < r)
    (hκ0 : 0 < κ) (hκ1 : κ ≤ 1 / 12) (hκD : κ * (12 * D) = p - 1)
    (hslo : (r - κ * r) ^ 2 ≤ s) :
    0 < 8 * (p - 1) * s - 4 * (r ^ 2 + κ * r ^ 2 - s) * D := by
  have hκr : κ * r ≤ r / 12 := by
    have := mul_le_mul_of_nonneg_right hκ1 hr.le
    linarith
  have h0 : r / 2 ≤ r - κ * r := by linarith
  have hs4 : r ^ 2 / 4 ≤ s := by
    have := mul_self_le_mul_self (by positivity) h0
    nlinarith
  have hBs : r ^ 2 + κ * r ^ 2 - s ≤ 3 * κ * r ^ 2 := by
    have e0 : (r - κ * r) ^ 2 = r ^ 2 - 2 * (κ * r ^ 2) + κ ^ 2 * r ^ 2 := by ring
    have : 0 ≤ κ ^ 2 * r ^ 2 := by positivity
    linarith
  have e1 : 2 * (p - 1) * r ^ 2 ≤ 8 * (p - 1) * s := by
    have := mul_le_mul_of_nonneg_left hs4 (by linarith : (0 : ℝ) ≤ 8 * (p - 1))
    linarith
  have e2 : 4 * (r ^ 2 + κ * r ^ 2 - s) * D ≤ (p - 1) * r ^ 2 := by
    have := mul_le_mul_of_nonneg_right hBs (by linarith : (0 : ℝ) ≤ 4 * D)
    have e : 3 * κ * r ^ 2 * (4 * D) = (p - 1) * r ^ 2 := by rw [← hκD]; ring
    linarith
  have hp1 : 0 < p - 1 := by linarith
  have : 0 < (p - 1) * r ^ 2 := by positivity
  linarith

/-! ## The strong maximum principle -/

set_option maxHeartbeats 800000 in
-- A long geometric argument; its arithmetic is in the lemmas above.
/-- **The strong maximum principle on a ball**, for an upper semicontinuous
function whose superjets with nonzero gradient satisfy the subsolution
inequality. -/
theorem smp_ball_jet (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p) {Ω : Set (EuclSpace d)}
    {u : EuclSpace d → ℝ} (husc : UpperSemicontinuousOn u Ω)
    (hjetc : ∀ w ∈ Ω, ∀ (q : EuclSpace d) (X : Bilin d), (q, X) ∈ SuperJet u w →
      q ≠ 0 → viscF p q X ≤ 0)
    {x : EuclSpace d} {R : ℝ} (hR : 0 < R) (hball : ball x R ⊆ Ω)
    (hmax : ∀ y ∈ ball x R, u y ≤ u x) :
    ∀ y ∈ ball x (R / 3), u y = u x := by
  intro y₀ hy₀
  by_contra hne
  set m := u x with hm
  have hy₀x : dist y₀ x < R / 3 := hy₀
  have hy₀R : y₀ ∈ ball x R := ball_subset_ball (by linarith) hy₀
  have hlt : u y₀ < m := lt_of_le_of_ne (hmax y₀ hy₀R) hne
  -- the ball K around y₀
  have hK : closedBall y₀ (R / 2) ⊆ ball x R := by
    intro y hy
    rw [mem_closedBall] at hy
    rw [mem_ball]
    calc dist y x ≤ dist y y₀ + dist y₀ x := dist_triangle _ _ _
      _ < R := by linarith
  -- the contact set
  set S := closedBall y₀ (R / 2) ∩ {y | m ≤ u y} with hSdef
  have hxS : x ∈ S :=
    ⟨by rw [mem_closedBall, dist_comm]; linarith, by change m ≤ u x; exact le_rfl⟩
  have hSc : IsClosed S := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    have hyK : y ∈ closedBall y₀ (R / 2) :=
      closure_minimal inter_subset_left isClosed_closedBall hy
    refine ⟨hyK, ?_⟩
    change m ≤ u y
    by_contra hcon
    push Not at hcon
    have hyΩ : y ∈ Ω := hball (hK hyK)
    have hev := husc y hyΩ m hcon
    rw [eventually_nhdsWithin_iff] at hev
    have hN : {y' | y' ∈ Ω → u y' < m} ∩ ball x R ∈ 𝓝 y :=
      inter_mem hev (isOpen_ball.mem_nhds (hK hyK))
    obtain ⟨z, ⟨hz1, hz2⟩, hzS⟩ := mem_closure_iff_nhds.1 hy _ hN
    have h1 : u z < m := hz1 (hball hz2)
    have h2 : m ≤ u z := hzS.2
    linarith
  have hScpt : IsCompact S :=
    (isCompact_closedBall y₀ (R / 2)).of_isClosed_subset hSc inter_subset_left
  have hSne : S.Nonempty := ⟨x, hxS⟩
  have hy₀S : y₀ ∉ S := fun h => by have : m ≤ u y₀ := h.2; linarith
  -- the nearest contact point
  set r := infDist y₀ S with hrdef
  have hr : 0 < r := (hSc.notMem_iff_infDist_pos hSne).1 hy₀S
  have hrx : r < R / 3 := by
    have := infDist_le_dist_of_mem (x := y₀) hxS
    linarith
  obtain ⟨z, hzS, hzd⟩ := hScpt.exists_infDist_eq_dist hSne y₀
  have hzr : dist z y₀ = r := by rw [dist_comm, ← hzd]
  have hin : ∀ y, dist y y₀ < r → u y < m := by
    intro y hy
    have hyK : y ∈ closedBall y₀ (R / 2) := by rw [mem_closedBall]; linarith
    by_contra hcon
    push Not at hcon
    have hyS : y ∈ S := ⟨hyK, hcon⟩
    have := infDist_le_dist_of_mem (x := y₀) hyS
    rw [dist_comm] at this
    linarith
  have huz : u z = m := le_antisymm (hmax z (hK hzS.1)) hzS.2
  -- the parameters
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdp : 0 < (d : ℝ) + p - 2 := by linarith
  set κ := (p - 1) / (12 * ((d : ℝ) + p - 2)) with hκdef
  have hκ0 : 0 < κ := div_pos (by linarith) (by positivity)
  have hκ12 : κ * (12 * ((d : ℝ) + p - 2)) = p - 1 := by
    rw [hκdef]; field_simp
  have hκ1 : κ ≤ 1 / 12 := by
    rw [hκdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hκr : κ * r ≤ r / 12 := by
    have := mul_le_mul_of_nonneg_right hκ1 hr.le
    linarith
  set θ := κ * r with hθ
  have hθ0 : 0 < θ := mul_pos hκ0 hr
  set B := r ^ 2 + κ * r ^ 2 with hB
  -- the gap on the inner ball
  have hCsub : closedBall y₀ (r - θ) ⊆ closedBall y₀ (R / 2) :=
    closedBall_subset_closedBall (by linarith)
  have hCΩ : closedBall y₀ (r - θ) ⊆ Ω := fun y hy => hball (hK (hCsub hy))
  obtain ⟨y₁, hy₁C, hy₁max⟩ := UpperSemicontinuousOn.exists_isMaxOn
    ⟨y₀, mem_closedBall_self (by linarith)⟩ (isCompact_closedBall y₀ (r - θ))
    (husc.mono hCΩ)
  have hy₁lt : u y₁ < m := hin y₁ (by rw [mem_closedBall] at hy₁C; linarith)
  set δ := m - u y₁ with hδ
  have hδ0 : 0 < δ := by linarith
  have hgapC : ∀ y ∈ closedBall y₀ (r - θ), u y ≤ m - δ := fun y hy => by
    have h' : u y ≤ u y₁ := hy₁max hy
    linarith
  -- ε
  set M₀ := 9 * κ ^ 2 * r ^ 4 with hM₀
  have hM₀0 : 0 ≤ M₀ := by positivity
  set ε := δ / (2 * (M₀ + 1)) with hεdef
  have hε0 : 0 < ε := by positivity
  have hεM : ε * M₀ ≤ δ / 2 := by
    rw [hεdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    have : 0 ≤ δ := hδ0.le
    linarith
  -- the barrier on the annulus and at z
  have hbar_le : ∀ y, r - θ ≤ dist y y₀ → dist y y₀ ≤ r → barrier y₀ B y ≤ M₀ := by
    intro y h1 h2
    unfold barrier
    rw [← dist_eq_norm]
    exact barrier_annulus_bound hr hκ0 hκ1 h1 h2
  have hbar_z : barrier y₀ B z = (κ * r ^ 2) ^ 2 := by
    unfold barrier
    rw [← dist_eq_norm, hzr, hB]
    ring
  -- the annulus
  set A := closedBall y₀ r ∩ {y | r - θ ≤ dist y y₀} with hAdef
  have hAc : IsCompact A :=
    (isCompact_closedBall y₀ r).inter_right
      (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hzA : z ∈ A := ⟨by rw [mem_closedBall, hzr], by
    change r - θ ≤ dist z y₀
    rw [hzr]; linarith⟩
  have hAΩ : A ⊆ Ω := fun y hy =>
    hball (hK (closedBall_subset_closedBall (by linarith) hy.1))
  -- the maximizer of g = u + ε φ
  set g : EuclSpace d → ℝ := fun y => u y + ε * barrier y₀ B y with hgdef
  have hgusc : UpperSemicontinuousOn g A := by
    have h1 := husc.mono hAΩ
    have h2 : Continuous (fun y => ε * barrier y₀ B y) := by
      unfold barrier; fun_prop
    exact h1.add (h2.upperSemicontinuous.upperSemicontinuousOn A)
  obtain ⟨w, hwA, hwmax⟩ := UpperSemicontinuousOn.exists_isMaxOn ⟨z, hzA⟩ hAc hgusc
  have hgz : g z = m + ε * (κ * r ^ 2) ^ 2 := by
    change u z + ε * barrier y₀ B z = _
    rw [huz, hbar_z]
  have hgw : g z ≤ g w := hwmax hzA
  have hwr : dist w y₀ ≤ r := by
    have := hwA.1
    rwa [mem_closedBall] at this
  -- w is not on the inner sphere
  have hwd : r - θ < dist w y₀ := by
    by_contra hcon
    push Not at hcon
    have hwC : w ∈ closedBall y₀ (r - θ) := by rw [mem_closedBall]; exact hcon
    have h1 := hgapC w hwC
    have h2 := hbar_le w hwA.2 hwr
    have h3 : g w ≤ m - δ + ε * M₀ := by
      change u w + ε * barrier y₀ B w ≤ _
      have := mul_le_mul_of_nonneg_left h2 hε0.le
      linarith
    have h4 : 0 ≤ ε * (κ * r ^ 2) ^ 2 := by positivity
    linarith
  -- w is a local maximum of g
  set ρ₀ := min (dist w y₀ - (r - θ)) (κ * r / 2) with hρ₀
  have hρ₀pos : 0 < ρ₀ := lt_min (by linarith) (by positivity)
  have hloc : ∀ᶠ y in 𝓝 w, u y + ε * barrier y₀ B y ≤ u w + ε * barrier y₀ B w := by
    filter_upwards [Metric.ball_mem_nhds w hρ₀pos] with y hy
    rw [mem_ball] at hy
    have hy1 : dist y w < dist w y₀ - (r - θ) := lt_of_lt_of_le hy (min_le_left _ _)
    have hy2 : dist y w < κ * r / 2 := lt_of_lt_of_le hy (min_le_right _ _)
    have hyd1 : r - θ < dist y y₀ := by
      have := dist_triangle w y y₀
      rw [dist_comm w y] at this
      linarith
    have hyd2 : dist y y₀ < r + κ * r / 2 := by
      have := dist_triangle y w y₀
      linarith
    by_cases hyr : dist y y₀ ≤ r
    · have hyA : y ∈ A := ⟨by rw [mem_closedBall]; exact hyr, hyd1.le⟩
      exact hwmax hyA
    · push Not at hyr
      have hyK : y ∈ closedBall y₀ (R / 2) := by
        rw [mem_closedBall]; linarith
      have huy : u y ≤ m := hmax y (hK hyK)
      have hby : barrier y₀ B y ≤ (κ * r ^ 2) ^ 2 := by
        unfold barrier
        rw [← dist_eq_norm]
        exact barrier_outside_bound hr hκ0 hκ1 hyr hyd2
      have h1 : u y + ε * barrier y₀ B y ≤ m + ε * (κ * r ^ 2) ^ 2 := by
        have := mul_le_mul_of_nonneg_left hby hε0.le
        linarith
      have h2 : g z ≤ u w + ε * barrier y₀ B w := hgw
      linarith
  -- the jet at w, and the contradiction
  have hwn : ‖w - y₀‖ = dist w y₀ := (dist_eq_norm w y₀).symm
  have hv0 : w - y₀ ≠ 0 := by
    intro h
    rw [h, norm_zero] at hwn
    linarith
  have hsr : ‖w - y₀‖ ^ 2 ≤ r ^ 2 := by
    rw [hwn, sq, sq]; exact mul_self_le_mul_self dist_nonneg hwr
  have hc : 0 < 4 * ε * (B - ‖w - y₀‖ ^ 2) := by
    have h1 : 0 < κ * r ^ 2 := mul_pos hκ0 (pow_pos hr 2)
    have : 0 < B - ‖w - y₀‖ ^ 2 := by rw [hB]; linarith
    positivity
  have hjet := superJet_barrier (u := u) (w := w) (y₀ := y₀) (B := B) hε0 hloc
  have hw : w ∈ Ω := hAΩ hwA
  have hq : (4 * ε * (B - ‖w - y₀‖ ^ 2)) • (w - y₀) ≠ 0 := smul_ne_zero hc.ne' hv0
  have hvisc := hjetc w hw _ _ hjet hq
  change _ ≤ (0 : ℝ) at hvisc
  rw [viscF_barrierJet hv0 hc] at hvisc
  -- the value is positive
  have hslo : (r - θ) ^ 2 ≤ ‖w - y₀‖ ^ 2 := by
    rw [hwn, sq, sq]; exact mul_self_le_mul_self (by linarith) hwd.le
  rw [hB] at hvisc
  set s := ‖w - y₀‖ ^ 2 with hs
  have hpos0 := smp_value_pos hp hdp hr hκ0 hκ1 hκ12 hslo
  have hpos := mul_pos hε0 hpos0
  have eq : -((4 * ε * (r ^ 2 + κ * r ^ 2 - s) * d - 8 * ε * s)
      + (p - 2) * (4 * ε * (r ^ 2 + κ * r ^ 2 - s) - 8 * ε * s))
      = ε * (8 * (p - 1) * s - 4 * (r ^ 2 + κ * r ^ 2 - s) * ((d : ℝ) + p - 2)) := by ring
  linarith


/-- **The strong maximum principle on a ball.** -/
theorem smp_ball (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p) {Ω : Set (EuclSpace d)}
    {u : EuclSpace d → ℝ} (hsub : IsViscositySubsolution p Ω (fun _ => 0) u)
    {x : EuclSpace d} {R : ℝ} (hR : 0 < R) (hball : ball x R ⊆ Ω)
    (hmax : ∀ y ∈ ball x R, u y ≤ u x) :
    ∀ y ∈ ball x (R / 3), u y = u x :=
  smp_ball_jet hd hp hsub.usc (fun _ hw _ _ hj hq => superJet_regular hd hp hsub hw hj hq)
    hR hball hmax

end

end PLaplacian
