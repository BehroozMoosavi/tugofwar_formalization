/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.PenaltyP

@[expose] public section

/-! # The semiconvex core, from Jensen's lemma and Alexandrov's theorem

Let `û` and `-v̌` be semiconvex with constant `λ`, and let

  `W(ξ, ζ) = û(ξ) - v̌(ζ) - P(ξ - ζ)`

have a strict global maximum at the origin. For each `n` this file finds a
point `(ξₙ, ζₙ)` within `1/(n+1)` of the origin, a superjet `(aₙ, Xₙ)` of `û`
at `ξₙ` and a subjet `(bₙ, Yₙ)` of `v̌` at `ζₙ`, with

  `Xₙ ≤ Yₙ`,  `-λ ≤ Xₙ`,  `Yₙ ≤ λ`,  `‖aₙ‖, ‖bₙ‖ = O(1/(n+1))`.

1. `W` is semiconvex on the product: it splits into `û + (λ/2)‖·‖²` in the
   first variable, `-v̌ + (λ/2)‖·‖²` in the second, and the quadratic part of
   the penalty, convex by `convexOn_quadPart`.
2. Jensen's lemma gives a set of positive measure in the ball of radius
   `1/(n+1)` of maxima of `W` plus small linear functions.
3. Alexandrov's theorem, transported to the product along the coordinate
   projections, makes both convolutions Peano twice differentiable almost
   everywhere, so some point of the Jensen set has both.
4. At that point, `CoreLines` gives `Xₙ ≤ Yₙ` and the gradients, and
   semiconvexity the bounds on the forms.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- Superjet congruence. -/
theorem superJet_congr {f g : EuclSpace d → ℝ} (hfg : f = g) {x q : EuclSpace d}
    {X : Bilin d} (h : (q, X) ∈ SuperJet f x) : (q, X) ∈ SuperJet g x := by
  subst hfg; exact h

/-- The expansion of the squared norm about a point. -/
theorem norm_sq_about (x y : EuclSpace d) :
    ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ 2 := by
  have h := norm_add_sq_real x (y - x)
  rw [show x + (y - x) = y by abel] at h
  exact h

/-- **Subtracting `(λ/2)‖·‖²` shifts a superjet** by `(-λ x, -λ I)`. -/
theorem superJet_sub_halfsq {f : EuclSpace d → ℝ} {x q : EuclSpace d}
    {X : Bilin d} (lam : ℝ) (h : (q, X) ∈ SuperJet f x) :
    (q + (-lam) • x, X + (-lam) • idForm d)
      ∈ SuperJet (fun y => f y - lam / 2 * ‖y‖ ^ 2) x := by
  intro η hη
  filter_upwards [h η hη] with y hy
  change f y ≤ f x + inner ℝ q (y - x) + (1 / 2) * (X (y - x)) (y - x)
    + η * ‖y - x‖ ^ 2 at hy
  change f y - lam / 2 * ‖y‖ ^ 2 ≤ f x - lam / 2 * ‖x‖ ^ 2
    + inner ℝ (q + (-lam) • x) (y - x)
    + (1 / 2) * ((X + (-lam) • idForm d) (y - x)) (y - x) + η * ‖y - x‖ ^ 2
  rw [add_form_apply, smul_form_apply, idForm_apply, inner_add_left,
    real_inner_smul_left]
  have hexp : lam / 2 * ‖y‖ ^ 2 = lam / 2 * ‖x‖ ^ 2 + lam * inner ℝ x (y - x)
      + lam / 2 * ‖y - x‖ ^ 2 := by rw [norm_sq_about x y]; ring
  linarith

/-- **Subtracting `(λ/2)‖·‖²` shifts a subjet** by `(-λ x, -λ I)`. -/
theorem subJet_sub_halfsq {f : EuclSpace d → ℝ} {x q : EuclSpace d}
    {X : Bilin d} (lam : ℝ) (h : (q, X) ∈ SubJet f x) :
    (q + (-lam) • x, X + (-lam) • idForm d)
      ∈ SubJet (fun y => f y - lam / 2 * ‖y‖ ^ 2) x := by
  intro η hη
  filter_upwards [h η hη] with y hy
  change f x + inner ℝ q (y - x) + (1 / 2) * (X (y - x)) (y - x)
    - η * ‖y - x‖ ^ 2 ≤ f y at hy
  change f x - lam / 2 * ‖x‖ ^ 2 + inner ℝ (q + (-lam) • x) (y - x)
    + (1 / 2) * ((X + (-lam) • idForm d) (y - x)) (y - x) - η * ‖y - x‖ ^ 2
    ≤ f y - lam / 2 * ‖y‖ ^ 2
  rw [add_form_apply, smul_form_apply, idForm_apply, inner_add_left,
    real_inner_smul_left]
  have hexp : lam / 2 * ‖y‖ ^ 2 = lam / 2 * ‖x‖ ^ 2 + lam * inner ℝ x (y - x)
      + lam / 2 * ‖y - x‖ ^ 2 := by rw [norm_sq_about x y]; ring
  linarith

section core

variable {u v : EuclSpace d → ℝ} {lam s r α : ℝ} {h0 : EuclSpace d}

/-- The doubled function without perturbation. -/
def dblW0 (u v : EuclSpace d → ℝ) (s r α : ℝ) (h0 : EuclSpace d)
    (z : EuclSpace d × EuclSpace d) : ℝ :=
  u z.1 - v z.2 - penP s r α h0 (z.1 - z.2)

theorem penP_zero (s r α : ℝ) (h0 : EuclSpace d) : penP s r α h0 0 = 0 := by
  simp [penP, penQ]

/-- **The doubled function is semiconvex on the product.** -/
theorem convexOn_dblW0 (_hlam : 0 ≤ lam) (hu : SemiconvexWith lam u)
    (hv : SemiconvexWith lam (fun y => -v y)) (hs : 0 ≤ s) (hr : 0 ≤ r)
    (hα : 0 < α) :
    ConvexOn ℝ univ (fun z => dblW0 u v s r α h0 z
      + (lam + 4 * penM s r α h0) / 2 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)) := by
  have c1 : ConvexOn ℝ univ
      (fun z : EuclSpace d × EuclSpace d => u z.1 + lam / 2 * ‖z.1‖ ^ 2) := by
    refine ⟨convex_univ, fun z₁ _ z₂ _ a b ha hb hab => ?_⟩
    have := hu.2 (mem_univ z₁.1) (mem_univ z₂.1) ha hb hab
    simpa only [Prod.fst_add, Prod.smul_fst] using this
  have c2 : ConvexOn ℝ univ
      (fun z : EuclSpace d × EuclSpace d => -v z.2 + lam / 2 * ‖z.2‖ ^ 2) := by
    refine ⟨convex_univ, fun z₁ _ z₂ _ a b ha hb hab => ?_⟩
    have := hv.2 (mem_univ z₁.2) (mem_univ z₂.2) ha hb hab
    simpa only [Prod.snd_add, Prod.smul_snd] using this
  have c3 := convexOn_quadPart (h0 := h0) hs hr hα (le_refl (4 * penM s r α h0))
  have hsum := (c1.add c2).add c3
  have heq : (fun z => dblW0 u v s r α h0 z
        + (lam + 4 * penM s r α h0) / 2 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2))
      = (fun z : EuclSpace d × EuclSpace d => u z.1 + lam / 2 * ‖z.1‖ ^ 2)
        + (fun z : EuclSpace d × EuclSpace d => -v z.2 + lam / 2 * ‖z.2‖ ^ 2)
        + (fun z : EuclSpace d × EuclSpace d =>
            4 * penM s r α h0 / 2 * (‖z.1‖ ^ 2 + ‖z.2‖ ^ 2)
              - penP s r α h0 (z.1 - z.2)) := by
    funext z
    simp only [dblW0, Pi.add_apply]
    ring
  rw [heq]
  exact hsum

/-- **One point of the core**, at scale `1/(n+1)`. -/
theorem core_point (hA : AlexandrovThm d) (hJ : JensenLemma d) (hlam : 0 < lam)
    (hu : SemiconvexWith lam u) (hv : SemiconvexWith lam (fun y => -v y))
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hα : 0 < α)
    (hstrict : ∀ z : EuclSpace d × EuclSpace d, z ≠ 0 →
      dblW0 u v s r α h0 z < dblW0 u v s r α h0 0)
    (n : ℕ) :
    ∃ ξ ζ a b : EuclSpace d, ∃ X Y : Bilin d,
      (a, X) ∈ SuperJet u ξ ∧ (b, Y) ∈ SubJet v ζ ∧
      ‖ξ‖ < 1 / ((n : ℝ) + 1) ∧ ‖ζ‖ < 1 / ((n : ℝ) + 1) ∧
      ‖a‖ ≤ (4 * penM s r α h0 + 1) * (1 / ((n : ℝ) + 1)) ∧
      ‖b‖ ≤ (4 * penM s r α h0 + 1) * (1 / ((n : ℝ) + 1)) ∧
      QuadLE X Y ∧
      (∀ w, -lam * ‖w‖ ^ 2 ≤ (X w) w) ∧ (∀ w, (Y w) w ≤ lam * ‖w‖ ^ 2) := by
  set rn : ℝ := 1 / ((n : ℝ) + 1) with hrn
  have hrnpos : 0 < rn := by rw [hrn]; positivity
  set M := penM s r α h0 with hM
  have hM0 : 0 ≤ M := penM_nonneg hs hr hα
  -- Jensen
  have hconv := convexOn_dblW0 (h0 := h0) hlam.le hu hv hs hr hα
  have hpos := hJ (dblW0 u v s r α h0) (lam + 4 * M) hconv 0 rn hrnpos
    (fun z _ hz => hstrict z hz) rn hrnpos
  -- Alexandrov, on the product
  have hAu := hA (fun ξ => u ξ + lam / 2 * ‖ξ‖ ^ 2) hu
  have hAv := hA (fun ζ => -v ζ + lam / 2 * ‖ζ‖ ^ 2) hv
  have hprod : ∀ᵐ z ∂(volume : Measure (EuclSpace d × EuclSpace d)),
      (∃ q X, TwiceDiffAt (fun ξ => u ξ + lam / 2 * ‖ξ‖ ^ 2) z.1 q X) ∧
      (∃ q X, TwiceDiffAt (fun ζ => -v ζ + lam / 2 * ‖ζ‖ ^ 2) z.2 q X) := by
    rw [Measure.volume_eq_prod]
    exact (Measure.quasiMeasurePreserving_fst.ae hAu).and
      (Measure.quasiMeasurePreserving_snd.ae hAv)
  obtain ⟨z, hzK, ⟨q₁, X₁, hT1⟩, ⟨q₂, X₂, hT2⟩⟩ := exists_mem_of_pos_of_ae' hpos hprod
  obtain ⟨hzball, p₁, p₂, hp₁, hp₂, hlmax⟩ := hzK
  have hzn : ‖z‖ < rn := mem_ball_zero_iff.1 hzball
  set ξ := z.1 with hξ
  set ζ := z.2 with hζ
  have hξn : ‖ξ‖ < rn := lt_of_le_of_lt (norm_fst_le z) hzn
  have hζn : ‖ζ‖ < rn := lt_of_le_of_lt (norm_snd_le z) hzn
  have hmax : IsLocalMax (dblW u v (penP s r α h0) p₁ p₂) (ξ, ζ) := hlmax
  -- the jets of u
  have hfu : (fun y => (fun ξ => u ξ + lam / 2 * ‖ξ‖ ^ 2) y - lam / 2 * ‖y‖ ^ 2)
      = u := by funext y; simp only; ring
  have hsupU := superJet_congr hfu (superJet_sub_halfsq lam hT1.1)
  have hsubU := subJet_congr hfu (subJet_sub_halfsq lam hT1.2)
  -- the jets of -v, then of v
  have hfv : (fun y => (fun ζ => -v ζ + lam / 2 * ‖ζ‖ ^ 2) y - lam / 2 * ‖y‖ ^ 2)
      = fun y => -v y := by funext y; simp only; ring
  have hsupNV := superJet_congr hfv (superJet_sub_halfsq lam hT2.1)
  have hsubNV := subJet_congr hfv (subJet_sub_halfsq lam hT2.2)
  have hnn : (fun y => -(fun y => -v y) y) = v := by funext y; simp
  have hsubV := subJet_congr hnn (subJet_neg_of_superJet hsupNV)
  have hsupV := superJet_congr hnn (superJet_neg_of_subJet hsubNV)
  -- the core line arguments
  have hTay : ∀ k, penP s r α h0 (ξ - ζ + k)
      ≤ penP s r α h0 (ξ - ζ) + inner ℝ (penG s r α h0 (ξ - ζ)) k + M * ‖k‖ ^ 2 :=
    fun k => penP_taylor hs hα (ξ - ζ) k
  have hdiag := core_diag hmax hsubU hsupV
  have hga := core_grad_u hmax hsubU hTay
  have hgb := core_grad_v hmax hsupV hTay
  refine ⟨ξ, ζ, _, _, _, _, hsupU, hsubV, hξn, hζn, ?_, ?_, hdiag, ?_, ?_⟩
  · -- the gradient of u
    rw [hga]
    have hg := norm_penG_le (h0 := h0) hs hr hα (ξ - ζ)
    have hd : ‖ξ - ζ‖ ≤ ‖ξ‖ + ‖ζ‖ := norm_sub_le _ _
    calc ‖penG s r α h0 (ξ - ζ) - p₁‖ ≤ ‖penG s r α h0 (ξ - ζ)‖ + ‖p₁‖ :=
          norm_sub_le _ _
      _ ≤ 2 * M * (‖ξ‖ + ‖ζ‖) + rn := by
          have := mul_le_mul_of_nonneg_left hd (by positivity : (0:ℝ) ≤ 2 * M)
          linarith
      _ ≤ (4 * M + 1) * rn := by nlinarith
  · -- the gradient of v
    rw [hgb]
    have hg := norm_penG_le (h0 := h0) hs hr hα (ξ - ζ)
    have hd : ‖ξ - ζ‖ ≤ ‖ξ‖ + ‖ζ‖ := norm_sub_le _ _
    calc ‖penG s r α h0 (ξ - ζ) + p₂‖ ≤ ‖penG s r α h0 (ξ - ζ)‖ + ‖p₂‖ :=
          norm_add_le _ _
      _ ≤ 2 * M * (‖ξ‖ + ‖ζ‖) + rn := by
          have := mul_le_mul_of_nonneg_left hd (by positivity : (0:ℝ) ≤ 2 * M)
          linarith
      _ ≤ (4 * M + 1) * rn := by nlinarith
  · -- the lower bound on X
    exact fun w => semiconvex_superJet hu hsupU w
  · -- the upper bound on Y
    intro w
    have h := semiconvex_superJet hv hsupNV w
    rw [neg_form_apply]
    linarith

/-- **The core, as sequences.** -/
theorem core_sequences (hA : AlexandrovThm d) (hJ : JensenLemma d)
    (hlam : 0 < lam) (hu : SemiconvexWith lam u)
    (hv : SemiconvexWith lam (fun y => -v y))
    (hs : 0 ≤ s) (hr : 0 ≤ r) (hα : 0 < α)
    (hstrict : ∀ z : EuclSpace d × EuclSpace d, z ≠ 0 →
      dblW0 u v s r α h0 z < dblW0 u v s r α h0 0) :
    ∃ (ξs ζs as bs : ℕ → EuclSpace d) (Xs Ys : ℕ → Bilin d),
      (∀ n, (as n, Xs n) ∈ SuperJet u (ξs n)) ∧
      (∀ n, (bs n, Ys n) ∈ SubJet v (ζs n)) ∧
      Tendsto ξs atTop (𝓝 0) ∧ Tendsto ζs atTop (𝓝 0) ∧
      Tendsto as atTop (𝓝 0) ∧ Tendsto bs atTop (𝓝 0) ∧
      (∀ n, QuadLE (Xs n) (Ys n)) ∧
      (∀ n w, -lam * ‖w‖ ^ 2 ≤ (Xs n w) w) ∧
      (∀ n w, (Ys n w) w ≤ lam * ‖w‖ ^ 2) := by
  have h := fun n : ℕ => core_point hA hJ hlam hu hv hs hr hα hstrict n
  choose ξs ζs as bs Xs Ys hsup hsub hξ hζ ha hb hle hXl hYu using h
  have h0t : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hCt : Tendsto (fun n : ℕ => (4 * penM s r α h0 + 1) * (1 / ((n : ℝ) + 1)))
      atTop (𝓝 0) := by
    have := h0t.const_mul (4 * penM s r α h0 + 1)
    rw [mul_zero] at this
    exact this
  exact ⟨ξs, ζs, as, bs, Xs, Ys, hsup, hsub,
    squeeze_zero_norm (fun n => (hξ n).le) h0t,
    squeeze_zero_norm (fun n => (hζ n).le) h0t,
    squeeze_zero_norm ha hCt, squeeze_zero_norm hb hCt, hle, hXl, hYu⟩

end core

end

end PLaplacian
