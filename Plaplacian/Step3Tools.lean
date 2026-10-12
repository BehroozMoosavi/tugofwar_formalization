/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.PsiSemi

/-! # Tools for the third step

* **Translation.** `U(· + a)` is semiconvex with the same constant, and a superjet
  of `U(· + a)` at `y` is a superjet of `U` at `y + a`.
* **Subdivision.** If `g(h + k) ≥ g(h) - C|k|²` for every `h` in a ball, then `g`
  is constant on the ball: splitting a segment into `N` equal steps loses at most
  `C|Δ|²/N`.
* **The frontier.** A bounded nonempty open set in `ℝᵈ`, `d ≥ 1`, has nonempty
  frontier: otherwise it would be clopen, hence everything.
* **Monotonicity of `ψ`.** `ψ(s) - ψ(t) = (s - t)(1 - η(s + t))`, and
  `1 - η(s + t)` is the average of `ψ'(s)` and `ψ'(t)`.
-/

open Set Topology Filter Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-! ## Translation -/

/-- **Translation preserves semiconvexity.** -/
theorem semiconvex_translate {lam : ℝ} {U : EuclSpace d → ℝ} (h : SemiconvexWith lam U)
    (a : EuclSpace d) : SemiconvexWith lam (fun y => U (y + a)) := by
  have h1 : ConvexOn ℝ univ (fun y => U (y + a) + lam / 2 * ‖y + a‖ ^ 2) := by
    refine ⟨convex_univ, fun y₁ _ y₂ _ s t hs ht hst => ?_⟩
    have h0 := h.2 (mem_univ (y₁ + a)) (mem_univ (y₂ + a)) hs ht hst
    have e : s • (y₁ + a) + t • (y₂ + a) = s • y₁ + t • y₂ + (s + t) • a := by module
    rw [hst, one_smul] at e
    rw [e] at h0
    exact h0
  have h2 := convexOn_affine a (-lam) (-(lam / 2) * ‖a‖ ^ 2)
  refine (h1.add h2).congr fun y _ => ?_
  simp only [Pi.add_apply]
  rw [norm_add_sq_real, real_inner_comm]
  ring

/-- **A superjet of a translate is a superjet at the translated point.** -/
theorem superJet_translate {u : EuclSpace d → ℝ} {a y q : EuclSpace d} {X : Bilin d}
    (h : (q, X) ∈ SuperJet (fun z => u (z + a)) y) : (q, X) ∈ SuperJet u (y + a) := by
  have h' : ∀ η > 0, ∀ᶠ z in 𝓝 y, u (z + a) ≤ u (y + a) + inner ℝ q (z - y)
      + 1 / 2 * (X (z - y)) (z - y) + η * ‖z - y‖ ^ 2 := h
  intro η hη
  have hT : Tendsto (fun z : EuclSpace d => z - a) (𝓝 (y + a)) (𝓝 y) := by
    have h0 : Continuous (fun z : EuclSpace d => z - a) := by fun_prop
    have := h0.tendsto (y + a)
    simpa using this
  filter_upwards [hT.eventually (h' η hη)] with z hz
  have e1 : z - a + a = z := sub_add_cancel z a
  have e2 : z - a - y = z - (y + a) := by abel
  rw [e1, e2] at hz
  change u z ≤ u (y + a) + inner ℝ q (z - (y + a)) + 1 / 2 * (X (z - (y + a))) (z - (y + a))
    + η * ‖z - (y + a)‖ ^ 2
  exact hz

/-! ## Subdivision -/

/-- **A function that loses at most `C|k|²` per step is constant on a ball.** -/
theorem const_of_quad_lower {g : EuclSpace d → ℝ} {C ρ : ℝ} (hC : 0 ≤ C)
    (h : ∀ h₁ ∈ ball (0 : EuclSpace d) ρ, ∀ k, g h₁ - C * ‖k‖ ^ 2 ≤ g (h₁ + k)) :
    ∀ h₁ ∈ ball (0 : EuclSpace d) ρ, ∀ h₂ ∈ ball (0 : EuclSpace d) ρ, g h₁ ≤ g h₂ := by
  intro h₁ hh₁ h₂ hh₂
  set Δ := h₂ - h₁ with hΔ
  -- the points of the subdivision lie in the ball
  have hmem : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → h₁ + t • Δ ∈ ball (0 : EuclSpace d) ρ := by
    intro t ht0 ht1
    have := (convex_ball (0 : EuclSpace d) ρ) hh₁ hh₂ (by linarith : (0 : ℝ) ≤ 1 - t) ht0
      (by ring : (1 - t) + t = 1)
    have e : (1 - t) • h₁ + t • h₂ = h₁ + t • Δ := by rw [hΔ]; module
    rwa [e] at this
  -- the loss after j of N steps
  have key : ∀ N : ℕ, 0 < N → g h₁ - C * ‖Δ‖ ^ 2 / N ≤ g h₂ := by
    intro N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have step : ∀ j : ℕ, j ≤ N →
        g h₁ - C * j * ‖Δ‖ ^ 2 / (N : ℝ) ^ 2 ≤ g (h₁ + ((j : ℝ) / N) • Δ) := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ih =>
        intro hj
        have ih' := ih (by omega)
        have hjN : ((j : ℝ) / N) ≤ 1 := by
          rw [div_le_one hNr]; exact_mod_cast (by omega : j ≤ N)
        have hP := hmem ((j : ℝ) / N) (by positivity) hjN
        have h1 := h _ hP ((1 / (N : ℝ)) • Δ)
        have e : h₁ + ((j : ℝ) / N) • Δ + (1 / (N : ℝ)) • Δ
            = h₁ + (((j + 1 : ℕ) : ℝ) / N) • Δ := by
          rw [add_assoc, ← add_smul]
          congr 2
          push_cast
          ring
        rw [e] at h1
        have hk : ‖(1 / (N : ℝ)) • Δ‖ ^ 2 = ‖Δ‖ ^ 2 / (N : ℝ) ^ 2 := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
          field_simp
        rw [hk] at h1
        have e2 : C * ((j + 1 : ℕ) : ℝ) * ‖Δ‖ ^ 2 / (N : ℝ) ^ 2
            = C * j * ‖Δ‖ ^ 2 / (N : ℝ) ^ 2 + C * (‖Δ‖ ^ 2 / (N : ℝ) ^ 2) := by
          push_cast; ring
        rw [e2]
        linarith
    have hN' := step N le_rfl
    have e : h₁ + ((N : ℝ) / N) • Δ = h₂ := by
      rw [div_self hNr.ne', one_smul, hΔ]; abel
    rw [e] at hN'
    have e2 : C * (N : ℝ) * ‖Δ‖ ^ 2 / (N : ℝ) ^ 2 = C * ‖Δ‖ ^ 2 / N := by
      field_simp
    rw [e2] at hN'
    exact hN'
  -- let N grow
  by_contra hcon
  push Not at hcon
  set gap := g h₁ - g h₂ with hgap
  have hgap0 : 0 < gap := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (C * ‖Δ‖ ^ 2 / gap)
  have hN0 : 0 < N := by
    have : (0 : ℝ) ≤ C * ‖Δ‖ ^ 2 / gap := by positivity
    exact_mod_cast (lt_of_le_of_lt this hN)
  have h1 := key N hN0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  have h2 : C * ‖Δ‖ ^ 2 / N < gap := by
    rw [div_lt_iff₀ hNr]
    have := (div_lt_iff₀ hgap0).1 hN
    linarith
  linarith

/-! ## The frontier -/

/-- **A bounded nonempty open set in `ℝᵈ`, `d ≥ 1`, has nonempty frontier.** -/
theorem frontier_nonempty (hd : 0 < d) {G : Set (EuclSpace d)} (hG : IsOpen G)
    (hb : Bornology.IsBounded G) (hne : G.Nonempty) : (frontier G).Nonempty := by
  by_contra hfr
  rw [not_nonempty_iff_eq_empty] at hfr
  have hcl : closure G = G := by
    rw [closure_eq_interior_union_frontier, hfr, union_empty, hG.interior_eq]
  have hclosed : IsClosed G := closure_eq_iff_isClosed.1 hcl
  have huniv : G = univ := IsClopen.eq_univ ⟨hclosed, hG⟩ hne
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
  set e := EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) with he
  have hen : ‖e‖ = 1 := by rw [he]; simp
  have hmem : (|C| + 1) • e ∈ G := by rw [huniv]; exact mem_univ _
  have h1 := hC _ hmem
  rw [norm_smul, hen, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)] at h1
  have := le_abs_self C
  linarith

/-! ## Monotonicity of `ψ` -/

/-- **`ψ` is increasing where `ψ' > 0`.** -/
theorem psi_mono {η s t : ℝ} (hs : 0 < 1 - 2 * η * s) (ht : 0 < 1 - 2 * η * t)
    (h : s - η * s ^ 2 ≤ t - η * t ^ 2) : s ≤ t := by
  by_contra hcon
  push Not at hcon
  have e : (t - η * t ^ 2) - (s - η * s ^ 2) = (t - s) * (1 - η * (t + s)) := by ring
  have hpos : 0 < 1 - η * (t + s) := by linarith
  have hneg : (t - s) * (1 - η * (t + s)) < 0 := mul_neg_of_neg_of_pos (by linarith) hpos
  linarith

end

end PLaplacian
