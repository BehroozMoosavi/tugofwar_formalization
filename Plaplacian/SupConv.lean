/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.PenaltyTaylor

/-! # Sup-convolution

For `u` bounded above and `λ > 0`,

  `û(ξ) = sup_x (u(x) - (λ/2) ‖x - ξ‖²)`.

It regularizes `u` from above: `u ≤ û ≤ sup u`, and `û` is semiconvex, since
`û(ξ) + (λ/2)‖ξ‖² = sup_x (u(x) - (λ/2)‖x‖² + λ ⟪x, ξ⟫)` is a supremum of affine
functions of `ξ`. For `u` upper semicontinuous the supremum is attained, at a
point within a bounded distance of `ξ`.

The **magic property** [CIL92, Lemma A.5]: a superjet of `û` at `ξ` is a
superjet of `u` at any maximizer `x*`. If `u(x') - (λ/2)‖x' - ξ'‖²` is tested at
`ξ' = ξ + (x' - x*)`, the distance `‖x' - ξ'‖` stays equal to `‖x* - ξ‖`, so
the superjet inequality for `û` at `ξ` transfers to `u` at `x*` verbatim. And
the gradient there is `λ (x* - ξ)`, since `û` is touched from below at `ξ` by
the smooth function `ξ' ↦ u(x*) - (λ/2)‖x* - ξ'‖²`; this is what makes the
maximizers converge when the gradients do.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- **The sup-convolution.** -/
def supConv (lam : ℝ) (u : EuclSpace d → ℝ) (ξ : EuclSpace d) : ℝ :=
  ⨆ x : EuclSpace d, (u x - lam / 2 * ‖x - ξ‖ ^ 2)

section basic

variable {lam : ℝ} {u : EuclSpace d → ℝ}

theorem bddAbove_supConv_family (hlam : 0 ≤ lam) (hub : BddAbove (range u))
    (ξ : EuclSpace d) :
    BddAbove (range fun x => u x - lam / 2 * ‖x - ξ‖ ^ 2) := by
  obtain ⟨SU, hSU⟩ := hub
  refine ⟨SU, ?_⟩
  rintro _ ⟨x, rfl⟩
  change u x - lam / 2 * ‖x - ξ‖ ^ 2 ≤ SU
  have h1 : u x ≤ SU := hSU ⟨x, rfl⟩
  have h2 : 0 ≤ lam / 2 * ‖x - ξ‖ ^ 2 := by positivity
  linarith

theorem le_supConv (hlam : 0 ≤ lam) (hub : BddAbove (range u))
    (x ξ : EuclSpace d) : u x - lam / 2 * ‖x - ξ‖ ^ 2 ≤ supConv lam u ξ :=
  le_ciSup (bddAbove_supConv_family hlam hub ξ) x

/-- `u ≤ û`. -/
theorem self_le_supConv (hlam : 0 ≤ lam) (hub : BddAbove (range u))
    (ξ : EuclSpace d) : u ξ ≤ supConv lam u ξ := by
  have := le_supConv hlam hub ξ ξ
  simpa using this

/-- `û ≤ sup u`. -/
theorem supConv_le_bound (hlam : 0 ≤ lam) {SU : ℝ} (hSU : ∀ x, u x ≤ SU)
    (ξ : EuclSpace d) : supConv lam u ξ ≤ SU := by
  apply ciSup_le
  intro x
  have h1 := hSU x
  have h2 : 0 ≤ lam / 2 * ‖x - ξ‖ ^ 2 := by positivity
  linarith

/-- The affine identity behind semiconvexity. -/
theorem supConv_term_affine (x ξ : EuclSpace d) :
    u x - lam / 2 * ‖x - ξ‖ ^ 2 + lam / 2 * ‖ξ‖ ^ 2
      = u x - lam / 2 * ‖x‖ ^ 2 + lam * inner ℝ x ξ := by
  rw [norm_sub_sq_real]; ring

/-- **The sup-convolution is semiconvex.** -/
theorem semiconvex_supConv (hlam : 0 ≤ lam) (hub : BddAbove (range u)) :
    SemiconvexWith lam (supConv lam u) := by
  refine ⟨convex_univ, fun ξ₁ _ ξ₂ _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  set z := a • ξ₁ + b • ξ₂ with hz
  -- every term at z is the convex combination of the terms at ξ₁ and ξ₂
  have key : supConv lam u z ≤ a * (supConv lam u ξ₁ + lam / 2 * ‖ξ₁‖ ^ 2)
      + b * (supConv lam u ξ₂ + lam / 2 * ‖ξ₂‖ ^ 2) - lam / 2 * ‖z‖ ^ 2 := by
    apply ciSup_le
    intro x
    have e0 := supConv_term_affine (u := u) (lam := lam) x z
    have e1 := supConv_term_affine (u := u) (lam := lam) x ξ₁
    have e2 := supConv_term_affine (u := u) (lam := lam) x ξ₂
    have hin : inner ℝ x z = a * inner ℝ x ξ₁ + b * inner ℝ x ξ₂ := by
      rw [hz, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have h1 := le_supConv hlam hub x ξ₁
    have h2 := le_supConv hlam hub x ξ₂
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  linarith

end basic

section attain

variable {lam : ℝ} {u : EuclSpace d → ℝ}

/-- The term of the sup-convolution is upper semicontinuous. -/
theorem usc_supConv_term (hu : UpperSemicontinuous u) (ξ : EuclSpace d) :
    UpperSemicontinuous (fun x => u x - lam / 2 * ‖x - ξ‖ ^ 2) := by
  have hg : UpperSemicontinuous (fun x : EuclSpace d => -(lam / 2 * ‖x - ξ‖ ^ 2)) := by
    apply Continuous.upperSemicontinuous; fun_prop
  have heq : (fun x => u x - lam / 2 * ‖x - ξ‖ ^ 2)
      = fun x => u x + -(lam / 2 * ‖x - ξ‖ ^ 2) := by funext x; ring
  rw [heq]
  exact hu.add hg

/-- **The supremum is attained**, for `u` upper semicontinuous. -/
theorem supConv_attained (hlam : 0 < lam) (hu : UpperSemicontinuous u)
    (hub : BddAbove (range u)) (ξ : EuclSpace d) :
    ∃ xs, supConv lam u ξ = u xs - lam / 2 * ‖xs - ξ‖ ^ 2 := by
  have hub' := hub
  obtain ⟨SU, hSU⟩ := hub
  set K := {x : EuclSpace d | lam / 2 * ‖x - ξ‖ ^ 2 ≤ SU - u ξ} with hKdef
  have hξK : ξ ∈ K := by
    change lam / 2 * ‖ξ - ξ‖ ^ 2 ≤ SU - u ξ
    have := hSU ⟨ξ, rfl⟩
    simp only [sub_self, norm_zero]
    have h0 : (0:ℝ) ^ 2 = 0 := by norm_num
    rw [h0, mul_zero]
    linarith
  have hKcl : IsClosed K := isClosed_le (by fun_prop) continuous_const
  have hKb : Bornology.IsBounded K := by
    refine (isBounded_closedBall (x := ξ) (r := 2 * (SU - u ξ) / lam + 1)).subset ?_
    intro x hx
    have hx' : lam / 2 * ‖x - ξ‖ ^ 2 ≤ SU - u ξ := hx
    rw [mem_closedBall, dist_eq_norm]
    have hsq : ‖x - ξ‖ ^ 2 ≤ 2 * (SU - u ξ) / lam := by
      rw [le_div_iff₀ hlam]; linarith
    nlinarith [sq_nonneg (‖x - ξ‖ - 1), norm_nonneg (x - ξ)]
  have hKc : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKcl hKb
  obtain ⟨xs, _, hxsmax⟩ :=
    ((usc_supConv_term (lam := lam) hu ξ).upperSemicontinuousOn K).exists_isMaxOn
      ⟨ξ, hξK⟩ hKc
  refine ⟨xs, le_antisymm ?_ (le_supConv hlam.le hub' xs ξ)⟩
  apply ciSup_le
  intro x
  by_cases hx : x ∈ K
  · exact hxsmax hx
  · have h1 : SU - u ξ < lam / 2 * ‖x - ξ‖ ^ 2 := by
      by_contra h
      push Not at h
      exact hx h
    have h2 : u x ≤ SU := hSU ⟨x, rfl⟩
    have h3 : u ξ - lam / 2 * ‖ξ - ξ‖ ^ 2 ≤ u xs - lam / 2 * ‖xs - ξ‖ ^ 2 :=
      hxsmax hξK
    simp only [sub_self, norm_zero] at h3
    have h0 : (0:ℝ) ^ 2 = 0 := by norm_num
    rw [h0, mul_zero, sub_zero] at h3
    linarith

end attain

section magic

variable {lam : ℝ} {u : EuclSpace d → ℝ} {ξ xs p : EuclSpace d} {X : Bilin d}

/-- **The magic property**: a superjet of the sup-convolution at `ξ` is a
superjet of `u` at the maximizer. -/
theorem superJet_of_supConv (hlam : 0 ≤ lam) (hub : BddAbove (range u))
    (hmax : supConv lam u ξ = u xs - lam / 2 * ‖xs - ξ‖ ^ 2)
    (hj : (p, X) ∈ SuperJet (supConv lam u) ξ) :
    (p, X) ∈ SuperJet u xs := by
  intro η hη
  have hT : Tendsto (fun x' : EuclSpace d => ξ + (x' - xs)) (𝓝 xs) (𝓝 ξ) := by
    have h0 : Continuous (fun x' : EuclSpace d => ξ + (x' - xs)) := by fun_prop
    have := h0.tendsto xs
    simpa using this
  filter_upwards [hT.eventually (hj η hη)] with x' hx'
  change supConv lam u (ξ + (x' - xs)) ≤ supConv lam u ξ
    + inner ℝ p (ξ + (x' - xs) - ξ)
    + (1 / 2) * (X (ξ + (x' - xs) - ξ)) (ξ + (x' - xs) - ξ)
    + η * ‖ξ + (x' - xs) - ξ‖ ^ 2 at hx'
  change u x' ≤ u xs + inner ℝ p (x' - xs) + (1 / 2) * (X (x' - xs)) (x' - xs)
    + η * ‖x' - xs‖ ^ 2
  have e1 : ξ + (x' - xs) - ξ = x' - xs := by abel
  rw [e1] at hx'
  have hle := le_supConv hlam hub x' (ξ + (x' - xs))
  have e2 : x' - (ξ + (x' - xs)) = xs - ξ := by abel
  rw [e2] at hle
  linarith

/-- **The gradient at a superjet of the sup-convolution** is `λ (x* - ξ)`. -/
theorem supConv_grad (hlam : 0 ≤ lam) (hub : BddAbove (range u))
    (hmax : supConv lam u ξ = u xs - lam / 2 * ‖xs - ξ‖ ^ 2)
    (hj : (p, X) ∈ SuperJet (supConv lam u) ξ) :
    p = lam • (xs - ξ) := by
  set a := lam • (xs - ξ) - p with hadef
  -- along every line, the coefficient of t vanishes
  have hline : ∀ w : EuclSpace d, inner ℝ a w = 0 := by
    intro w
    apply eq_zero_of_eventually_mul_le
      (C := lam / 2 * ‖w‖ ^ 2 + (1 / 2) * (X w) w + ‖w‖ ^ 2)
    have hT : Tendsto (fun t : ℝ => ξ + t • w) (𝓝 0) (𝓝 ξ) := by
      have h0 : Continuous (fun t : ℝ => ξ + t • w) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have := h0.tendsto 0
      simpa using this
    filter_upwards [hT.eventually (hj 1 one_pos)] with t ht
    change supConv lam u (ξ + t • w) ≤ supConv lam u ξ + inner ℝ p (ξ + t • w - ξ)
      + (1 / 2) * (X (ξ + t • w - ξ)) (ξ + t • w - ξ)
      + 1 * ‖ξ + t • w - ξ‖ ^ 2 at ht
    have e1 : ξ + t • w - ξ = t • w := by abel
    rw [e1] at ht
    have hle := le_supConv hlam hub xs (ξ + t • w)
    have e2 : xs - (ξ + t • w) = (xs - ξ) - t • w := by abel
    rw [e2, norm_sub_sq_real] at hle
    simp only [inner_smul_right, map_smul, smul_eq_mul, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs, ContinuousLinearMap.smul_apply] at ht hle
    have ha : inner ℝ a w = lam * inner ℝ (xs - ξ) w - inner ℝ p w := by
      rw [hadef, inner_sub_left, real_inner_smul_left]
    rw [ha]
    nlinarith
  have h0 : inner ℝ a a = 0 := hline a
  have ha0 : a = 0 := inner_self_eq_zero.1 h0
  rw [hadef] at ha0
  exact (sub_eq_zero.1 ha0).symm

end magic

end

end PLaplacian
