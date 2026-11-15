/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Super

@[expose] public section

/-!
# The eigenvalue bounds for the singular case

A quadratic form is at most the largest eigenvalue times the squared norm, for
every vector, and the trace is at most the dimension times the largest
eigenvalue. Together they turn the reflection bound of the singular case,
which involves the positive part of the largest eigenvalue, into the
predicate inequality, which involves the eigenvalue itself: where the
eigenvalue is negative, the trace bound shows the case cannot occur.

The layer-two quadratic bound covers only a nonnegative eigenvalue and a
nonzero vector; the unconditional form is proved here, because the negative
case is exactly where the contradiction lives.

## Main results

- bddAbove_quad_sphere, quad_le_lamMax_norm
- laplacianOf_le_lamMax
- reflect_neg_of_envelope_pos
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The eigenvalue bounds for the singular case

The singular argument yields `0 ≤ (p-2) λ⁺ + tr X` with `λ⁺ = max λ_max 0`,
and must turn it into the predicate's `tr X + (p-2) λ_max ≥ 0`. Two facts do
it: a quadratic form is at most its largest eigenvalue times the squared norm,
for every vector; and the trace is at most the dimension times the largest
eigenvalue.

The second disposes of the case `λ_max < 0`. There the argument gives
`tr X ≥ 0`, but `tr X ≤ d λ_max < 0`, so the case cannot occur.

The layer-two bound `quad_le_lamMax_ball` covers only `λ_max ≥ 0` and nonzero
vectors; the unconditional form is proved here.
-/


/-- The values on the unit sphere are bounded above, by the operator norm. -/
theorem bddAbove_quad_sphere (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) :
    BddAbove ((fun v => (X v) v) '' {v : EuclSpace d | ‖v‖ = 1}) := by
  refine ⟨‖X‖, ?_⟩
  rintro a ⟨w, hw, rfl⟩
  simp only [Set.mem_ofPred_eq] at hw
  have h1 := X.le_opNorm w
  have h2 := (X w).le_opNorm w
  calc (X w) w ≤ |(X w) w| := le_abs_self _
    _ = ‖(X w) w‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖X w‖ * ‖w‖ := h2
    _ ≤ (‖X‖ * ‖w‖) * ‖w‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = ‖X‖ := by rw [hw]; ring

/-- **A quadratic form is at most the largest eigenvalue times the squared
norm**, for every vector. -/
theorem quad_le_lamMax_norm (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ)
    (z : EuclSpace d) : (X z) z ≤ lamMax X * ‖z‖ ^ 2 := by
  by_cases hz : z = 0
  · subst hz; simp
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    set v := ‖z‖⁻¹ • z with hvdef
    have hv : ‖v‖ = 1 := by
      rw [hvdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hn)]
    have hle : (X v) v ≤ lamMax X :=
      le_csSup (bddAbove_quad_sphere X) ⟨v, hv, rfl⟩
    have hzv : z = ‖z‖ • v := by
      rw [hvdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hn), one_smul]
    have hexp : (X z) z = ‖z‖ ^ 2 * (X v) v := by
      conv_lhs => rw [hzv]
      simp
      ring
    rw [hexp]
    nlinarith [hle, sq_nonneg ‖z‖]

/-- **The trace is at most the dimension times the largest eigenvalue.** -/
theorem laplacianOf_le_lamMax (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) :
    laplacianOf X ≤ (d : ℝ) * lamMax X := by
  unfold laplacianOf
  have h : ∀ i : Fin d,
      (X (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1)
        ≤ lamMax X := by
    intro i
    have := quad_le_lamMax_norm X (EuclideanSpace.single i 1)
    simpa using this
  calc ∑ i, (X (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1)
      ≤ ∑ _i : Fin d, lamMax X := Finset.sum_le_sum (fun i _ => h i)
    _ = (d : ℝ) * lamMax X := by
        simp [Finset.sum_const]

/-- **The reflection quantity is negative when the envelope is positive.** -/
theorem reflect_neg_of_envelope_pos {p : ℝ} (_hp : 2 ≤ p) (hd : 0 < d)
    {X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ}
    (hpos : 0 < viscFLower p X) :
    (p - 2) * max (lamMax X) 0 + laplacianOf X < 0 := by
  unfold viscFLower at hpos
  by_cases h : 0 ≤ lamMax X
  · rw [max_eq_left h]; linarith
  · push Not at h
    rw [max_eq_right (le_of_lt h), mul_zero, zero_add]
    have htr := laplacianOf_le_lamMax X
    have hd' : (0:ℝ) < d := by exact_mod_cast hd
    have : (d : ℝ) * lamMax X < 0 := mul_neg_of_pos_of_neg hd' h
    linarith

end

end PLaplacian
