/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Plaplacian.Measurability

/-!
# The key estimate for the comparison principle

This file proves the analytic content of the comparison principle of
Luiro--Parviainen--Saksman (*On the existence and uniqueness of `p`-harmonious
functions*, Differential Integral Equations 27 (2014), Thm. 2.2): for two
solutions of the dynamic programming principle,

  `v x - u x ≤ α * sup_{B ε x} (v - u) + β * ⨍_{B ε x} (v - u)`.

Weighting the two difference estimates of `Plaplacian.Measurability` by `α/2`
each produces the factor `α` on the supremum term.

## Why not a perturbation argument

The informal remedy for the non-strictness of nonexpansiveness is to perturb by
a strictly concave function. That route is unavailable: `T_ε` is neither sub-
nor superadditive, since the supremum is subadditive while the infimum is
superadditive, so the pair `sup + inf` is neither. Hence
`T_ε (u + δψ) ≤ T_ε u + δ T_ε ψ` fails in both directions and the perturbation
cannot be split off. See the withdrawn section of `Plaplacian.Perturbation`.
LPS avoid perturbing altogether.

## Main results

- `BddMeas.sub`: the admissible class is closed under differences.
- `key_estimate`: the estimate above.

## TODO

The remainder of LPS Thm. 2.2 is topological rather than estimative: set
`M = sup_Ω (v - u)` and `G = {x | (v - u) x = M}`, deduce from `key_estimate`
that `G` is non-empty and that `|B ε x \ G| = 0` for every `x ∈ G`, and observe
that this propagation contradicts boundedness of `Ω`.
-/

open MeasureTheory Metric Set

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-- The difference of two admissible functions is admissible. -/
lemma BddMeas.sub {u v : EuclSpace d → ℝ} (hu : BddMeas u) (hv : BddMeas v) :
    BddMeas (fun y => u y - v y) := by
  obtain ⟨Cu, hCu⟩ := hu.bound
  obtain ⟨Cv, hCv⟩ := hv.bound
  refine ⟨hu.meas.sub hv.meas, ⟨Cu + Cv, fun y => ?_⟩⟩
  calc |u y - v y| ≤ |u y| + |v y| := abs_sub _ _
    _ ≤ Cu + Cv := by linarith [hCu y, hCv y]

/-- **The key estimate.** -/
theorem key_estimate (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ))
    {u v : EuclSpace d → ℝ} (hu : BddMeas u) (hv : BddMeas v)
    (x : EuclSpace d) :
    tugOfWarOp p ε v x - tugOfWarOp p ε u x
      ≤ (p - 2) / (p + (d : ℝ)) * sSup ((fun y => v y - u y) '' ball x ε)
        + ((d : ℝ) + 2) / (p + (d : ℝ))
            * ⨍ y in ball x ε, (v y - u y) := by
  have hne := nonempty_ball x hε
  have hdiff := hv.sub hu
  have hsup := sSup_sub_sSup_le u v (ball x ε) hne
    (hu.bddAbove_image (ball x ε)) (hdiff.bddAbove_image (ball x ε))
  have hinf := sInf_sub_sInf_le u v (ball x ε) hne
    (hv.bddBelow_image (ball x ε)) (hdiff.bddAbove_image (ball x ε))
  have havg : (⨍ y in ball x ε, v y) - (⨍ y in ball x ε, u y)
      = ⨍ y in ball x ε, (v y - u y) := by
    rw [show (fun y : EuclSpace d => v y - u y) = v - u from rfl,
        MeasureTheory.setAverage_sub (hv.integrableOn_ball x ε)
          (hu.integrableOn_ball x ε)]
  have hα : 0 ≤ (p - 2) / (p + (d : ℝ)) / 2 := by
    apply div_nonneg (div_nonneg (by linarith) hpd.le); norm_num
  unfold tugOfWarOp
  rw [← havg]
  nlinarith [hsup, hinf, hα]



/-! ### The a.e.-equality step

LPS deduce from `key_estimate` that if `v - u` attains its maximum `M` at `x`,
then `v - u = M` almost everywhere on `B ε x`. The mechanism is that a function
bounded above by `M` whose average equals `M` must equal `M` a.e., which
reduces via `M - f` to the standard fact that a nonnegative integrable function
with vanishing integral is zero a.e.
-/

/-- A nonnegative integrable function with vanishing integral is zero a.e. -/
lemma ae_eq_zero_of_setIntegral_eq_zero
    {g : EuclSpace d → ℝ} {s : Set (EuclSpace d)}
    (hint : MeasureTheory.IntegrableOn g s) (hnn : ∀ y, 0 ≤ g y)
    (hzero : (∫ y in s, g y) = 0) :
    g =ᵐ[volume.restrict s] 0 := by
  refine (MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae ?_ hint).1 hzero
  exact Filter.Eventually.of_forall hnn

/-- **The a.e.-equality step.** A function bounded above by `M` whose average
over a ball equals `M` is equal to `M` almost everywhere on that ball. -/
theorem ae_eq_of_setAverage_eq_max
    {f : EuclSpace d → ℝ} {M : ℝ} (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε)
    (hint : MeasureTheory.IntegrableOn f (ball x ε))
    (hle : ∀ y, f y ≤ M)
    (havg : (⨍ y in ball x ε, f y) = M) :
    (fun y => M - f y) =ᵐ[volume.restrict (ball x ε)] 0 := by
  have hcint : MeasureTheory.IntegrableOn (fun _ : EuclSpace d => M)
      (ball x ε) := integrableOn_const
  have hgint : MeasureTheory.IntegrableOn (fun y => M - f y) (ball x ε) :=
    hcint.sub hint
  refine ae_eq_zero_of_setIntegral_eq_zero hgint
    (fun y => by linarith [hle y]) ?_
  have hsub : (⨍ y in ball x ε, (M - f y)) = 0 := by
    rw [show (fun y : EuclSpace d => M - f y)
          = (fun _ : EuclSpace d => M) - f from rfl,
        MeasureTheory.setAverage_sub hcint hint,
        setAverage_const_ball M x hε, havg, sub_self]
  rw [MeasureTheory.setAverage_eq] at hsub
  have hvol : volume.real (ball x ε) ≠ 0 := by
    have h1 : volume (ball x ε) ≠ 0 := measure_ball_ne_zero x hε
    have h2 : volume (ball x ε) ≠ ⊤ := measure_ball_lt_top.ne
    simp only [MeasureTheory.Measure.real]
    exact ne_of_gt (ENNReal.toReal_pos h1 h2)
  rw [smul_eq_mul, mul_eq_zero] at hsub
  rcases hsub with h | h
  · exact absurd (inv_eq_zero.1 h) hvol
  · exact h



/-! ### The propagation step

LPS conclude by showing that the set `G` where `v - u` attains its maximum
propagates: if `x ∈ G` then `|B ε x \ G| = 0`, and hence `G` contains a point
displaced from `x` by roughly `ε / 2` in any fixed direction. Iterating produces
points of `G` with unbounded first coordinate, contradicting boundedness of
`Ω`.

The ingredients are collected here. The measure-theoretic core is
`nonempty_inter_of_ae_full`: a set of full measure in a ball must meet every
positive-measure subset of that ball.
-/

/-- The displaced small ball sits inside the big one. -/
theorem ball_displaced_subset (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε)
    (e : EuclSpace d) (he : ‖e‖ = 1) :
    ball (x + (ε / 2) • e) (ε / 4) ⊆ ball x ε := by
  intro y hy
  rw [mem_ball, dist_eq_norm] at hy ⊢
  have h1 : ‖y - x‖ ≤ ‖y - (x + (ε / 2) • e)‖ + ‖(ε / 2 : ℝ) • e‖ := by
    have hrw : y - x = (y - (x + (ε / 2) • e)) + (ε / 2 : ℝ) • e := by abel
    rw [hrw]
    exact norm_add_le _ _
  have h2 : ‖(ε / 2 : ℝ) • e‖ = ε / 2 := by
    rw [norm_smul, he, Real.norm_eq_abs, abs_of_nonneg (by linarith), mul_one]
  linarith

/-- **A set of full measure in a ball meets every positive-measure subset.** -/
theorem nonempty_inter_of_ae_full (G : Set (EuclSpace d)) (x : EuclSpace d)
    {ε : ℝ} (hfull : volume (ball x ε \ G) = 0)
    (S : Set (EuclSpace d)) (hS : S ⊆ ball x ε) (hSpos : 0 < volume S) :
    (G ∩ S).Nonempty := by
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hsub : S ⊆ ball x ε \ G := by
    intro y hy
    refine ⟨hS hy, fun hyG => ?_⟩
    have hmem : y ∈ G ∩ S := ⟨hyG, hy⟩
    rw [hcon] at hmem
    exact hmem
  have hle : volume S ≤ volume (ball x ε \ G) := measure_mono hsub
  rw [hfull, nonpos_iff_eq_zero] at hle
  exact hSpos.ne' hle

/-- A unit vector exists in dimension at least one; needed to fix a marching
direction. -/
theorem exists_unit_vector (hd : 0 < d) : ∃ e : EuclSpace d, ‖e‖ = 1 := by
  refine ⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ), ?_⟩
  simp

/-- **The propagation step.** If `G` has full measure in `B ε x`, it contains a
point displaced from `x` by `ε / 2` in the direction `e`, up to `ε / 4`. -/
theorem exists_mem_displaced (G : Set (EuclSpace d)) (x : EuclSpace d)
    {ε : ℝ} (hε : 0 < ε) (e : EuclSpace d) (he : ‖e‖ = 1)
    (hfull : volume (ball x ε \ G) = 0) :
    (G ∩ ball (x + (ε / 2) • e) (ε / 4)).Nonempty :=
  nonempty_inter_of_ae_full G x hfull _
    (ball_displaced_subset x hε e he)
    (measure_ball_pos volume _ (by linarith))



/-! ### The unboundedness contradiction

Each propagation step advances `⟪e, ·⟫` by at least `ε / 4`, since the
displacement is `ε / 2` and the ball has radius `ε / 4`. Iterating shows `G` is
unbounded in the direction `e`, which contradicts `G ⊆ Ω` for bounded `Ω`.
This closes the comparison principle of Luiro--Parviainen--Saksman.
-/

/-- Each step advances the inner product with `e` by at least `ε / 4`. -/
theorem inner_advance (x y : EuclSpace d)
    (e : EuclSpace d) (he : ‖e‖ = 1) {ε : ℝ}
    (hy : y ∈ ball (x + (ε / 2) • e) (ε / 4)) :
    inner ℝ e x + ε / 4 ≤ inner ℝ e y := by
  have hd : ‖y - (x + (ε / 2) • e)‖ < ε / 4 := by
    rw [← dist_eq_norm]; exact mem_ball.1 hy
  have hip : inner ℝ e (y - (x + (ε / 2) • e)) ≥ -(ε / 4) := by
    have h1 := abs_real_inner_le_norm e (y - (x + (ε / 2) • e))
    rw [he, one_mul] at h1
    have h2 := abs_le.1 h1
    linarith [h2.1]
  have hexp : inner ℝ e (y - (x + (ε / 2) • e))
      = inner ℝ e y - inner ℝ e x - (ε / 2) := by
    have hee : inner ℝ e e = (1 : ℝ) := by
      rw [real_inner_self_eq_norm_sq, he, one_pow]
    rw [inner_sub_right, inner_add_right, real_inner_smul_right, hee]
    ring
  linarith [hip, hexp]

/-- One step of the march. -/
theorem exists_advance (G : Set (EuclSpace d)) {ε : ℝ} (hε : 0 < ε)
    (e : EuclSpace d) (he : ‖e‖ = 1)
    (hprop : ∀ x ∈ G, volume (ball x ε \ G) = 0)
    {x : EuclSpace d} (hx : x ∈ G) :
    ∃ y ∈ G, inner ℝ e x + ε / 4 ≤ inner ℝ e y := by
  obtain ⟨y, hyG, hyB⟩ := exists_mem_displaced G x hε e he (hprop x hx)
  exact ⟨y, hyG, inner_advance x y e he hyB⟩

/-- **`G` is unbounded in the direction `e`.** -/
theorem exists_far (G : Set (EuclSpace d)) {ε : ℝ} (hε : 0 < ε)
    (e : EuclSpace d) (he : ‖e‖ = 1)
    (hprop : ∀ x ∈ G, volume (ball x ε \ G) = 0)
    {x₀ : EuclSpace d} (hx₀ : x₀ ∈ G) (k : ℕ) :
    ∃ y ∈ G, inner ℝ e x₀ + k * (ε / 4) ≤ inner ℝ e y := by
  induction k with
  | zero => exact ⟨x₀, hx₀, by simp⟩
  | succ n ih =>
      obtain ⟨y, hyG, hy⟩ := ih
      obtain ⟨z, hzG, hz⟩ := exists_advance G hε e he hprop hyG
      refine ⟨z, hzG, ?_⟩
      push_cast
      linarith

/-- **The contradiction.** A non-empty set with the propagation property
cannot have `⟪e, ·⟫` bounded above, so it cannot be contained in a bounded
set. -/
theorem not_bddAbove_inner (G : Set (EuclSpace d)) {ε : ℝ} (hε : 0 < ε)
    (e : EuclSpace d) (he : ‖e‖ = 1)
    (hprop : ∀ x ∈ G, volume (ball x ε \ G) = 0)
    {x₀ : EuclSpace d} (hx₀ : x₀ ∈ G) (R : ℝ) :
    ∃ y ∈ G, R < inner ℝ e y := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((R - inner ℝ e x₀) / (ε / 4))
  obtain ⟨y, hyG, hy⟩ := exists_far G hε e he hprop hx₀ k
  refine ⟨y, hyG, ?_⟩
  have hq : 0 < ε / 4 := by linarith
  have hk' : R - inner ℝ e x₀ < (k : ℝ) * (ε / 4) := by
    calc R - inner ℝ e x₀
        = ((R - inner ℝ e x₀) / (ε / 4)) * (ε / 4) := by field_simp
      _ < (k : ℝ) * (ε / 4) := by
          exact mul_lt_mul_of_pos_right hk hq
  linarith



/-! ### Rigidity at an attained maximum

If the difference attains its supremum at a point where both functions solve
the dynamic programming principle, the key estimate forces the *average* to
attain the supremum too, and hence by `ae_eq_of_setAverage_eq_max` the
difference equals the supremum almost everywhere on the ball. This is the
propagation property required by `exists_mem_displaced`.

The step where `α + β = 1` and `β > 0` are both essential: from
`M ≤ α · sup + β · avg` with `sup ≤ M`, one concludes `avg ≥ M` only because
the weights sum to one and the average carries positive weight.
-/

/-- At a point where the difference attains its supremum and both functions are
fixed by the operator, the average over the ball also attains the supremum. -/
theorem ae_full_of_attains (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ))
    {u v : EuclSpace d → ℝ} (hu : BddMeas u) (hv : BddMeas v)
    {M : ℝ} (hMle : ∀ y, v y - u y ≤ M)
    {x : EuclSpace d} (hMx : v x - u x = M)
    (hfix : tugOfWarOp p ε v x - tugOfWarOp p ε u x = v x - u x) :
    (⨍ y in ball x ε, (v y - u y)) = M := by
  have hkey := key_estimate p ε hp hε hpd hu hv x
  rw [hfix, hMx] at hkey
  have hsup : sSup ((fun y => v y - u y) '' ball x ε) ≤ M := by
    refine csSup_le ⟨v x - u x, x, mem_ball_self hε, rfl⟩ ?_
    rintro a ⟨y, -, rfl⟩
    exact hMle y
  have havgle : (⨍ y in ball x ε, (v y - u y)) ≤ M := by
    have h0 : (⨍ _y in ball x ε, M) = M := setAverage_const_ball M x hε
    rw [← h0]
    exact setAverage_mono_ball x
      ((hv.sub hu).integrableOn_ball x ε) integrableOn_const hMle
  have hα : 0 ≤ (p - 2) / (p + (d : ℝ)) := div_nonneg (by linarith) hpd.le
  have hβ : 0 < ((d : ℝ) + 2) / (p + (d : ℝ)) := by positivity
  have hab : (p - 2) / (p + (d : ℝ)) + ((d : ℝ) + 2) / (p + (d : ℝ)) = 1 :=
    alpha_add_beta p hpd
  refine le_antisymm havgle ?_
  by_contra hcon
  push Not at hcon
  have hstep : (p - 2) / (p + (d : ℝ)) * sSup ((fun y => v y - u y) '' ball x ε)
      ≤ (p - 2) / (p + (d : ℝ)) * M :=
    mul_le_mul_of_nonneg_left hsup hα
  have hstep2 : ((d : ℝ) + 2) / (p + (d : ℝ))
        * (⨍ y in ball x ε, (v y - u y))
      < ((d : ℝ) + 2) / (p + (d : ℝ)) * M :=
    mul_lt_mul_of_pos_left hcon hβ
  have hsum : (p - 2) / (p + (d : ℝ)) * M
      + ((d : ℝ) + 2) / (p + (d : ℝ)) * M = M := by
    calc (p - 2) / (p + (d : ℝ)) * M + ((d : ℝ) + 2) / (p + (d : ℝ)) * M
        = ((p - 2) / (p + (d : ℝ)) + ((d : ℝ) + 2) / (p + (d : ℝ))) * M := by
          ring
      _ = 1 * M := by rw [hab]
      _ = M := one_mul M
  linarith [hkey, hstep, hstep2, hsum]

/-- **The propagation property.** Combining rigidity of the average with the
a.e.-equality step: at an attained maximum, the difference equals `M` almost
everywhere on the ball, i.e. the maximum set has full measure there. -/
theorem ae_eq_max_on_ball (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ))
    {u v : EuclSpace d → ℝ} (hu : BddMeas u) (hv : BddMeas v)
    {M : ℝ} (hMle : ∀ y, v y - u y ≤ M)
    {x : EuclSpace d} (hMx : v x - u x = M)
    (hfix : tugOfWarOp p ε v x - tugOfWarOp p ε u x = v x - u x) :
    (fun y => M - (v y - u y)) =ᵐ[volume.restrict (ball x ε)] 0 :=
  ae_eq_of_setAverage_eq_max x hε ((hv.sub hu).integrableOn_ball x ε) hMle
    (ae_full_of_attains p ε hp hε hpd hu hv hMle hMx hfix)

end PLaplacian
