/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.HessCont2

/-!
# The singular case

The lower-envelope inequality at a strict maximum of the upper relaxed limit
minus a bounded C three test function, and the upper-envelope inequality at a
strict minimum of the lower relaxed limit, the latter by transport.

The argument is a reflection. At the near-maximizer, the supremum of the test
function on the small ball is attained at some increment, and the infimum is
at most the value at the reflected increment; averaging cancels the linear
terms exactly, so no gradient enters and the inequality holds at every strict
maximum, not only where the gradient vanishes. The resulting bound involves the
positive part of the largest eigenvalue rather than the eigenvalue itself ---
which is why the stronger bound fails at a critical point --- and the
eigenvalue lemmas convert it to the predicate inequality.

The proof is long and its arithmetic was first written with nonlinear
arithmetic over a large context, which timed out. Expanding every product by an
explicit identity so that each step closes by linear arithmetic made it
tractable.

## Main results

- reflect_bound
- singular_subsol
- lamMax_neg
- singular_supsol
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The singular case

The lower-envelope inequality `viscFLower p (hess φ x₀) ≤ 0`, at a strict
maximum of the upper relaxed limit minus a bounded `C³` test function, and its
dual for the supersolution.

## The reflection argument

At the near-maximizer `y`, let `y + z` be where the test function attains its
supremum on the closed ball of radius `ε`. Then the infimum is at most the
value at the reflected point `y - z`, also in the ball, and averaging the two
cancels the linear terms exactly:

  `(sup + inf)/2 ≤ φ y + ½ D²φ(y)(z,z) + K ε³`.

No gradient enters, so nothing here requires the gradient to vanish: the
inequality holds at every strict maximum.

Bounding `D²φ(y)(z,z) ≤ (λ⁺ + η) ε²`, with `λ⁺ = max λ_max 0`, and pushing
through the comparison gives in the limit `0 ≤ (p-2) λ⁺ + tr X`. That involves
`λ⁺`, not `λ_max`, which is why the stronger `λ_max` bound fails at a critical
point --- but the eigenvalue lemmas convert it to the predicate's inequality.
-/

/-- **The reflection bound.** The average of the supremum and infimum over the
closed ball is at most the value plus half the Hessian on some increment of
norm at most `ε`, plus the Taylor error. -/
theorem reflect_bound {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    (y : EuclSpace d) {ε K : ℝ} (hε : 0 < ε)
    (hTerr : ∀ z : EuclSpace d, ‖z‖ ≤ ε → |taylorErr φ y z| ≤ K * ε ^ 3) :
    ∃ z : EuclSpace d, ‖z‖ ≤ ε ∧
      (sSup (φ '' closedBall y ε) + sInf (φ '' closedBall y ε)) / 2
        ≤ φ y + (1 / 2) * (fderiv ℝ (fderiv ℝ φ) y z) z + K * ε ^ 3 := by
  obtain ⟨w, hw, hsup⟩ := exists_sSup_closedBall hφ.continuous y hε
  set z := w - y with hzdef
  have hz : ‖z‖ ≤ ε := norm_sub_le_of_mem hw
  have hwz : w = y + z := by rw [hzdef]; abel
  -- the reflected point is in the ball, so the infimum is below its value
  have hmem : y + -z ∈ closedBall y ε := by
    rw [mem_closedBall, dist_eq_norm]
    have : y + -z - y = -z := by abel
    rw [this, norm_neg]; exact hz
  have hbdd : BddBelow (φ '' closedBall y ε) :=
    ((isCompact_closedBall y ε).image hφ.continuous).bddBelow
  have hinf : sInf (φ '' closedBall y ε) ≤ φ (y + -z) :=
    csInf_le hbdd ⟨y + -z, hmem, rfl⟩
  -- the two expansions
  have hplus := decomp_at φ y z
  have hminus := decomp_at φ y (-z)
  have hlin : fderiv ℝ φ y (-z) = - fderiv ℝ φ y z := map_neg _ _
  have hquad : (fderiv ℝ (fderiv ℝ φ) y (-z)) (-z)
      = (fderiv ℝ (fderiv ℝ φ) y z) z := by simp
  rw [hlin, hquad] at hminus
  -- the errors
  have he1 := (abs_le.1 (hTerr z hz)).2
  have he2 := (abs_le.1 (hTerr (-z) (by rw [norm_neg]; exact hz))).2
  refine ⟨z, hz, ?_⟩
  rw [hsup, hwz]
  linarith [hinf, hplus, hminus, he1, he2]

set_option maxHeartbeats 1000000 in
/-- **The singular subsolution inequality.** At a strict maximum of the upper
relaxed limit minus a bounded `C³` test function, the lower envelope is
nonpositive. No condition on the gradient is needed. -/
theorem singular_subsol [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε))
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ) (hφb : BddMeas φ)
    {B : ℝ} (hB : ∀ y, |φ y| ≤ B)
    {x₀ : EuclSpace d} {r : ℝ} (hr : 0 < r) (hΩ : closedBall x₀ r ⊆ Ω)
    (hstrict : IsStrictMaxOn (fun w => ubar u w - φ w) x₀ r) :
    viscFLower p (hess φ x₀) ≤ 0 := by
  by_contra hneg
  push Not at hneg
  set X := fderiv ℝ (fderiv ℝ φ) x₀ with hXdef
  have hQ := reflect_neg_of_envelope_pos hp hd (X := X) hneg
  set lp := max (lamMax X) 0 with hlpdef
  set γ := -((p - 2) * lp + laplacianOf X) with hγdef
  have hγ : 0 < γ := by rw [hγdef]; linarith
  have hp0 : 0 < p := by linarith
  -- the Hessian, uniformly near the maximum
  obtain ⟨ρ₁, hρ₁, hhess⟩ :=
    hess_quad_cont hφ x₀ (by positivity : (0:ℝ) < γ / (4 * p))
  -- the Laplacian, near the maximum
  have hlapc := continuousAt_laplacianOf (hφ.of_le (by norm_num)) x₀
  have hev1 : ∀ᶠ y in nhds x₀,
      laplacianOf (fderiv ℝ (fderiv ℝ φ) y) < laplacianOf X + γ / 4 :=
    hlapc.eventually (eventually_lt_nhds (by linarith))
  rw [Metric.eventually_nhds_iff] at hev1
  obtain ⟨ρ₂, hρ₂, hlap⟩ := hev1
  -- the uniform Taylor and average constants
  obtain ⟨K₀, hK₀⟩ := taylorErr_le_cubic_uniform hφ x₀ r
  obtain ⟨Ka₀, hKa₀⟩ := avgErr_uniform hφ x₀ r
  set K := max K₀ 0 with hKdef
  set Ka := max Ka₀ 0 with hKadef
  have hK : 0 ≤ K := le_max_right _ _
  have hKa : 0 ≤ Ka := le_max_right _ _
  -- the weights
  set α := (p - 2) / (p + (d : ℝ)) with hαdef
  set β := ((d : ℝ) + 2) / (p + (d : ℝ)) with hβdef
  have hα : 0 ≤ α := by rw [hαdef]; exact div_nonneg (by linarith) hpd.le
  have hβ : 0 ≤ β := by rw [hβdef]; positivity
  set Cc := α * K + β * Ka + 1 with hCcdef
  have hCc : 0 < Cc := by rw [hCcdef]; positivity
  -- the radius for the near-maximizer
  set ρ := min (min ρ₁ ρ₂) (r / 2) with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]; exact lt_min (lt_min hρ₁ hρ₂) (by linarith)
  have hex : ∀ ε : ℝ, 0 < ε → ∃ z ∈ closedBall x₀ r,
      sSup ((fun w => u ε w - φ w) '' closedBall x₀ r) - ε ^ 3
        < u ε z - φ z :=
    fun ε hε => exists_near_sup_cube u hC hB x₀ hr hε
  choose! y hymem hynear using hex
  have hfreq := nearmax_frequently_in_ball u hC hφ.continuous hB hr hρ
    hstrict y (fun ε hε => ⟨hymem ε hε, hynear ε hε⟩)
  -- the eventual conditions
  have hlt : ∀ {a : ℝ}, 0 < a →
      ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε < a := by
    intro a ha
    exact Filter.mem_of_superset (Ioo_mem_nhdsGT ha) (fun x hx => hx.2)
  have hpos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
    self_mem_nhdsWithin
  set τ := γ / (4 * (p + (d : ℝ)) * Cc) with hτdef
  have hτ : 0 < τ := by rw [hτdef]; positivity
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ε < r / 2 ∧ ε < τ ∧ 0 < ε :=
    (hlt (by linarith : (0:ℝ) < r / 2)).and ((hlt hτ).and hpos)
  obtain ⟨ε, hyball, hεr, hετ, hε⟩ := (hfreq.and_eventually hev).exists
  -- the near-maximizer's position
  have hyρ : dist (y ε) x₀ < ρ := hyball
  have hy₁ : y ε ∈ ball x₀ ρ₁ := by
    rw [mem_ball]
    exact lt_of_lt_of_le hyρ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hy₂ : dist (y ε) x₀ < ρ₂ :=
    lt_of_lt_of_le hyρ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hyr : dist (y ε) x₀ < r / 2 := lt_of_lt_of_le hyρ (min_le_right _ _)
  have hyc : y ε ∈ closedBall x₀ r := hymem ε hε
  have hεR : ε ≤ r := by linarith
  -- the Taylor error bound at the near-maximizer
  have hTerr : ∀ z : EuclSpace d, ‖z‖ ≤ ε →
      |taylorErr φ (y ε) z| ≤ K * ε ^ 3 := by
    intro z hz
    have h1 := hK₀ (y ε) hyc z (le_trans hz hεR)
    have hz3 : ‖z‖ ^ 3 ≤ ε ^ 3 := pow_le_pow_left₀ (norm_nonneg z) hz 3
    have hz3nn : (0:ℝ) ≤ ‖z‖ ^ 3 := by positivity
    have hA : K₀ * ‖z‖ ^ 3 ≤ K * ‖z‖ ^ 3 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hz3nn
    have hB : K * ‖z‖ ^ 3 ≤ K * ε ^ 3 := mul_le_mul_of_nonneg_left hz3 hK
    linarith [h1, hA, hB]
  -- the reflection bound
  obtain ⟨z, hz, hrefl⟩ := reflect_bound hφ (y ε) hε hTerr
  -- the Hessian quadratic form, bounded by the eigenvalue part
  have hq1 := hhess (y ε) hy₁ z
  have hq2 := quad_le_lamMax_norm X z
  have hz2 : ‖z‖ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hz2nn : (0:ℝ) ≤ ‖z‖ ^ 2 := by positivity
  have hlpge : lamMax X ≤ lp := le_max_left _ _
  have hlpnn : 0 ≤ lp := le_max_right _ _
  have hquad : (fderiv ℝ (fderiv ℝ φ) (y ε) z) z
      ≤ (lp + γ / (4 * p)) * ε ^ 2 := by
    have hA : lamMax X * ‖z‖ ^ 2 ≤ lp * ‖z‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hlpge hz2nn
    have hB : lp * ‖z‖ ^ 2 ≤ lp * ε ^ 2 :=
      mul_le_mul_of_nonneg_left hz2 hlpnn
    have hC : γ / (4 * p) * ‖z‖ ^ 2 ≤ γ / (4 * p) * ε ^ 2 :=
      mul_le_mul_of_nonneg_left hz2 (by positivity)
    have hexp : (lp + γ / (4 * p)) * ε ^ 2
        = lp * ε ^ 2 + γ / (4 * p) * ε ^ 2 := by ring
    rw [hexp]
    linarith [hq1, hq2, hA, hB, hC]
  -- the extreme-value part over the open ball
  have hext : (sSup (φ '' ball (y ε) ε) + sInf (φ '' ball (y ε) ε)) / 2
      ≤ φ (y ε) + (1 / 2) * ((lp + γ / (4 * p)) * ε ^ 2) + K * ε ^ 3 := by
    rw [sSup_ball_eq_closedBall hφ.continuous (y ε) hε,
      sInf_ball_eq_closedBall hφ.continuous (y ε) hε]
    linarith [hrefl, hquad]
  -- the average part
  have havgeq := setAverage_expansion hd (hφ.of_le (by norm_num)) (y ε) hε
  have havgerr := (abs_le.1 (hKa₀ (y ε) hyc ε hε hεR)).2
  have hε3 : (0:ℝ) ≤ ε ^ 3 := by positivity
  have hKa3 : Ka₀ * ε ^ 3 ≤ Ka * ε ^ 3 :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hε3
  have hlapy := hlap hy₂
  have hε2 : 0 < ε ^ 2 := by positivity
  have hcoefA : (0:ℝ) ≤ ε ^ 2 / (2 * ((d : ℝ) + 2)) := by positivity
  have havg : (⨍ w in ball (y ε) ε, φ w)
      ≤ φ (y ε) + ε ^ 2 / (2 * ((d : ℝ) + 2)) * (laplacianOf X + γ / 4)
        + Ka * ε ^ 3 := by
    rw [havgeq]
    have : ε ^ 2 / (2 * ((d : ℝ) + 2)) * laplacianOf (hess φ (y ε))
        ≤ ε ^ 2 / (2 * ((d : ℝ) + 2)) * (laplacianOf X + γ / 4) :=
      mul_le_mul_of_nonneg_left (le_of_lt hlapy) hcoefA
    linarith [havgerr, hKa3]
  -- the comparison at the near-maximizer
  have hyΩ : y ε ∈ Ω := hΩ hyc
  have hle : ∀ w ∈ ball (y ε) ε,
      u ε w - φ w ≤ sSup ((fun w => u ε w - φ w) '' closedBall x₀ r) := by
    intro w hw
    have hwc : w ∈ closedBall x₀ r := by
      rw [mem_closedBall]
      rw [mem_ball] at hw
      have := dist_triangle w (y ε) x₀
      linarith
    exact le_sup_on_ball u hC hB x₀ w hwc
  have hcmp := dpp_comparison_approx hp hε hpd (hu ε hε) hφb hyΩ hle
    (le_of_lt (hynear ε hε))
  rw [tugOfWarOp_eq] at hcmp
  -- combine: the weights sum to one, and the bracket is at most -γ/2
  have hsum : α + β = 1 := by
    rw [hαdef, hβdef]; field_simp; ring
  have hc1 : α * ((1 / 2) * ((lp + γ / (4 * p)) * ε ^ 2))
      = ε ^ 2 / (2 * (p + (d : ℝ))) * ((p - 2) * (lp + γ / (4 * p))) := by
    rw [hαdef]; field_simp
  have hc2 : β * (ε ^ 2 / (2 * ((d : ℝ) + 2)) * (laplacianOf X + γ / 4))
      = ε ^ 2 / (2 * (p + (d : ℝ))) * (laplacianOf X + γ / 4) := by
    rw [hβdef]; field_simp
  have hbr : (p - 2) * (lp + γ / (4 * p)) + (laplacianOf X + γ / 4)
      ≤ -(γ / 2) := by
    have : (p - 2) * (γ / (4 * p)) ≤ γ / 4 := by
      have hpγ : (p - 2) * (γ / (4 * p)) ≤ p * (γ / (4 * p)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      have : p * (γ / (4 * p)) = γ / 4 := by field_simp
      linarith
    have hexp : (p - 2) * (lp + γ / (4 * p))
        = (p - 2) * lp + (p - 2) * (γ / (4 * p)) := by ring
    rw [hexp]
    linarith [this, hγdef]
  have hc : 0 < ε ^ 2 / (2 * (p + (d : ℝ))) := by positivity
  have hfin : α * ((sSup (φ '' ball (y ε) ε) + sInf (φ '' ball (y ε) ε)) / 2)
      + β * (⨍ w in ball (y ε) ε, φ w)
      ≤ φ (y ε) + ε ^ 2 / (2 * (p + (d : ℝ))) * (-(γ / 2))
        + (α * K + β * Ka) * ε ^ 3 := by
    have h1 := mul_le_mul_of_nonneg_left hext hα
    have h2 := mul_le_mul_of_nonneg_left havg hβ
    have h3 := mul_le_mul_of_nonneg_left hbr (le_of_lt hc)
    have e1 : α * (φ (y ε) + (1 / 2) * ((lp + γ / (4 * p)) * ε ^ 2)
          + K * ε ^ 3)
        = α * φ (y ε) + α * ((1 / 2) * ((lp + γ / (4 * p)) * ε ^ 2))
          + α * K * ε ^ 3 := by ring
    have e2 : β * (φ (y ε) + ε ^ 2 / (2 * ((d : ℝ) + 2))
          * (laplacianOf X + γ / 4) + Ka * ε ^ 3)
        = β * φ (y ε) + β * (ε ^ 2 / (2 * ((d : ℝ) + 2))
          * (laplacianOf X + γ / 4)) + β * Ka * ε ^ 3 := by ring
    have e3 : ε ^ 2 / (2 * (p + (d : ℝ)))
          * ((p - 2) * (lp + γ / (4 * p)) + (laplacianOf X + γ / 4))
        = ε ^ 2 / (2 * (p + (d : ℝ))) * ((p - 2) * (lp + γ / (4 * p)))
          + ε ^ 2 / (2 * (p + (d : ℝ))) * (laplacianOf X + γ / 4) := by ring
    have e4 : α * φ (y ε) + β * φ (y ε) = φ (y ε) := by
      rw [← add_mul, hsum, one_mul]
    have e5 : (α * K + β * Ka) * ε ^ 3 = α * K * ε ^ 3 + β * Ka * ε ^ 3 := by
      ring
    rw [e1] at h1
    rw [e2] at h2
    rw [e3] at h3
    linarith [h1, h2, h3, hc1, hc2, e4, e5]
  -- the parameter is small enough that the cube does not compensate
  have hsmall : Cc * ε ^ 3 < ε ^ 2 / (2 * (p + (d : ℝ))) * (γ / 2) := by
    have hετ' : Cc * ε < γ / (4 * (p + (d : ℝ))) := by
      have := mul_lt_mul_of_pos_left hετ hCc
      rw [hτdef] at this
      have hval : Cc * (γ / (4 * (p + (d : ℝ)) * Cc))
          = γ / (4 * (p + (d : ℝ))) := by field_simp
      linarith
    have hval2 : ε ^ 2 / (2 * (p + (d : ℝ))) * (γ / 2)
        = ε ^ 2 * (γ / (4 * (p + (d : ℝ)))) := by field_simp; ring
    rw [hval2]
    have : Cc * ε ^ 3 = ε ^ 2 * (Cc * ε) := by ring
    rw [this]
    exact mul_lt_mul_of_pos_left hετ' hε2
  have hCcexp : Cc * ε ^ 3 = (α * K + β * Ka) * ε ^ 3 + ε ^ 3 := by
    rw [hCcdef]; ring
  have hneg : ε ^ 2 / (2 * (p + (d : ℝ))) * (-(γ / 2))
      = -(ε ^ 2 / (2 * (p + (d : ℝ))) * (γ / 2)) := by ring
  linarith [hcmp, hfin, hsmall, hCcexp, hneg]

/-- The largest eigenvalue of a negated form is minus the smallest. -/
theorem lamMax_neg (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) :
    lamMax (-X) = - lamMin X := by
  unfold lamMax lamMin
  have hf : (fun v => ((-X) v) v) = fun v => -((X v) v) := by
    funext v; simp
  rw [hf]
  have := sInf_eq_neg_sSup (fun v => (X v) v) {v : EuclSpace d | ‖v‖ = 1}
  linarith

/-- **The singular supersolution inequality**, by transport. -/
theorem singular_supsol [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} {F : EuclSpace d → ℝ}
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε))
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ) (hφb : BddMeas φ)
    {B : ℝ} (hB : ∀ y, |φ y| ≤ B)
    {x₀ : EuclSpace d} {r : ℝ} (hr : 0 < r) (hΩ : closedBall x₀ r ⊆ Ω)
    (hmin : ∀ w ∈ closedBall x₀ r, w ≠ x₀ →
      lbar u x₀ - φ x₀ < lbar u w - φ w) :
    0 ≤ viscFUpper p (hess φ x₀) := by
  have hCn : ∀ ε y, |(fun ε y => -u ε y) ε y| ≤ C := by
    intro ε y; simp only; rw [abs_neg]; exact hC ε y
  have hun : ∀ ε > 0, IsPHarmonious p ε Ω (fun y => -F y)
      ((fun ε y => -u ε y) ε) :=
    fun ε hε => isPHarmonious_neg (hu ε hε)
  have hBn : ∀ y, |(fun y => -φ y) y| ≤ B := by
    intro y; simp only; rw [abs_neg]; exact hB y
  have hstrict : IsStrictMaxOn
      (fun w => ubar (fun ε y => -u ε y) w - (fun y => -φ y) w) x₀ r := by
    intro w hw hne
    have h1 := lbar_eq_neg_ubar_neg u w
    have h2 := lbar_eq_neg_ubar_neg u x₀
    have h3 := hmin w hw hne
    simp only
    linarith [h1, h2, h3]
  have h := singular_subsol hd hp hpd hCn hun (contDiff_neg' hφ)
    (bddMeas_neg hφb) hBn hr hΩ hstrict
  unfold viscFLower at h
  unfold viscFUpper
  rw [hess_eq_fderiv, hess_neg, laplacianOf_neg, lamMax_neg] at h
  rw [hess_eq_fderiv]
  linarith [h]

end

end PLaplacian
