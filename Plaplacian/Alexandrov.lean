/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.RiemannTaylor

/-! # Alexandrov's theorem

A convex function on `ℝᵈ` is twice differentiable, in the sense of Peano, at
almost every point.

At almost every `x` there is `y` with `J(y) = x`, `J` the proximal map,
differentiable at `y` with invertible derivative `B` (`ae_good`). With
`A = B⁻¹ - I` and the chosen subgradients, the linear approximation of the
subgradients (`subgrad_linear_approx`) is exactly the hypothesis of the
Riemann-sum expansion (`peano_of_approx`), which gives

  `f(x + h) = f(x) + ⟪p₀, h⟫ + ½ ⟪A h, h⟫ + o(‖h‖²)`.

The jet needs a bilinear form with quadratic form `⟪A h, h⟫`. It is built from
the matrix `⟪A bᵢ, bⱼ⟫` in an orthonormal basis, through `formOfMatrix`, which
avoids constructing `(u, w) ↦ ⟪A u, w⟫` from the inner product as a
semilinear map.

With Alexandrov's theorem proved, the comparison principle for strict
subsolutions rests on Jensen's lemma alone.
-/

open Set Topology Filter MeasureTheory Metric Finset

namespace PLaplacian

noncomputable section

variable {d : ℕ}



set_option synthInstance.maxHeartbeats 400000 in
-- Sums of forms and scalars, applied twice.
/-- **The quadratic form of `⟪A ·, ·⟫`, through its matrix.** -/
theorem quad_formOfMatrix (A : EuclSpace d →L[ℝ] EuclSpace d) (h : EuclSpace d) :
    (formOfMatrix (fun i j => inner ℝ (A (obasis d i)) (obasis d j)) h) h
      = inner ℝ (A h) h := by
  rw [formOfMatrix_apply]
  have hh := (obasis d).sum_repr' h
  calc ∑ i, ∑ j, inner ℝ (A (obasis d i)) (obasis d j)
        * (inner ℝ (obasis d i) h * inner ℝ (obasis d j) h)
      = inner ℝ (A (∑ i, inner ℝ (obasis d i) h • obasis d i))
          (∑ j, inner ℝ (obasis d j) h • obasis d j) := by
        simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left,
          real_inner_smul_right]
        conv_rhs => rw [Finset.sum_comm]
        exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
    _ = inner ℝ (A h) h := by rw [hh]

/-- **A Peano expansion gives Peano twice differentiability.** -/
theorem twiceDiffAt_of_expansion {f : EuclSpace d → ℝ} {x p0 : EuclSpace d}
    {X : Bilin d} {A : EuclSpace d →L[ℝ] EuclSpace d}
    (hX : ∀ h, (X h) h = inner ℝ (A h) h)
    (hexp : ∀ ε > 0, ∃ δ > 0, ∀ h : EuclSpace d, ‖h‖ < δ →
      |f (x + h) - f x - inner ℝ p0 h - 1 / 2 * inner ℝ (A h) h| ≤ ε * ‖h‖ ^ 2) :
    TwiceDiffAt f x p0 X := by
  constructor
  · intro η hη
    obtain ⟨δ, hδ, hb⟩ := hexp η hη
    filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
    rw [mem_ball, dist_eq_norm] at hy
    have h1 := (abs_le.1 (hb (y - x) hy)).2
    have e : x + (y - x) = y := by abel
    rw [e] at h1
    change f y ≤ f x + inner ℝ p0 (y - x) + 1 / 2 * (X (y - x)) (y - x)
      + η * ‖y - x‖ ^ 2
    rw [hX]
    linarith
  · intro η hη
    obtain ⟨δ, hδ, hb⟩ := hexp η hη
    filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
    rw [mem_ball, dist_eq_norm] at hy
    have h1 := (abs_le.1 (hb (y - x) hy)).1
    have e : x + (y - x) = y := by abel
    rw [e] at h1
    change f x + inner ℝ p0 (y - x) + 1 / 2 * (X (y - x)) (y - x)
      - η * ‖y - x‖ ^ 2 ≤ f y
    rw [hX]
    linarith

/-- **Alexandrov's theorem.** -/
theorem alexandrov : AlexandrovThm d := by
  intro f hf
  filter_upwards [ae_good hf] with x hx
  obtain ⟨y, hJy, hdiff, hdet, hp0⟩ := hx
  set B := fderiv ℝ (proxMap f) y with hB
  have hd : HasFDerivAt (proxMap f) B y := hdiff.hasFDerivAt
  obtain ⟨Binv, hinv, _⟩ := exists_inv_of_det hdet
  set A : EuclSpace d →L[ℝ] EuclSpace d := Binv - ContinuousLinearMap.id ℝ (EuclSpace d)
    with hA
  have hAapp : ∀ v, A v = Binv v - v := fun v => by
    rw [hA, sub_apply, ContinuousLinearMap.id_apply]
  -- the linear approximation, for the chosen subgradients
  have happrox : ∀ ε > 0, ∃ δ > 0, ∀ z, ‖z - x‖ < δ →
      ‖subgradSel f z - (y - x) - A (z - x)‖ ≤ ε * ‖z - x‖ := by
    intro ε hε
    obtain ⟨δ, hδ, hb⟩ := subgrad_linear_approx hf hJy hd hinv hp0 hε
    refine ⟨δ, hδ, fun z hz => ?_⟩
    rw [hAapp]
    exact hb z (subgradSel f z) hz (subgradSel_spec hf z)
  -- the expansion, and the jet
  have hexp := fun ε hε => peano_of_approx (subgradSel_spec hf) happrox (ε := ε) hε
  exact ⟨y - x, formOfMatrix (fun i j => inner ℝ (A (obasis d i)) (obasis d j)),
    twiceDiffAt_of_expansion (quad_formOfMatrix A) hexp⟩

/-- **The comparison principle for strict subsolutions, assuming only Jensen's
lemma.** -/
theorem comparison_strict_of_J (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p)
    (hJ : JensenLemma d) {Ω : Set (EuclSpace d)}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) {U V : EuclSpace d → ℝ}
    (hU : UpperSemicontinuous U) (hV : LowerSemicontinuous V)
    (hUb : BddAbove (range U)) (hVb : BddBelow (range V))
    {c : ℝ} (hc : 0 < c)
    (hsub : IsViscositySubsolution p Ω (fun _ => -c) U)
    (hsup : IsViscositySupersolution p Ω (fun _ => 0) V)
    (hbd : ∀ x ∈ frontier Ω, U x ≤ V x) :
    ∀ x ∈ Ω, U x ≤ V x :=
  comparison_strict_of_AJ hd hp alexandrov hJ hΩo hΩb hU hV hUb hVb hc hsub hsup hbd

end

end PLaplacian
