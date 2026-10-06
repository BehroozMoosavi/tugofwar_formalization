/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.CoreJA

/-! # Compactness of bounded forms, by coordinates

A sequence of forms with bounded entries has a subsequence converging in
operator norm. This is compactness in a finite-dimensional space, but it is not
proved in the space of forms itself: there, the operator norm and the metric of
the space of continuous linear maps give two structures that the elaborator
cannot reconcile (the extraction times out even with five times the default
budget). It is proved instead in coordinates, where nothing of the kind arises.

With an orthonormal basis `(bᵢ)`, a form is determined by its matrix
`Z(bᵢ, bⱼ)`, and the expansion `u = Σ ⟪bᵢ, u⟫ bᵢ` gives

  `‖Z‖ ≤ Σᵢⱼ |Z(bᵢ, bⱼ)|`.

The matrices of the sequence lie in a bounded set of `Fin d → Fin d → ℝ`, where
a convergent subsequence exists; the limit form is built from the limit matrix
as `Σᵢⱼ Aᵢⱼ ⟪bᵢ, ·⟫ ⊗ ⟪bⱼ, ·⟫`; and convergence of the entries gives
convergence in norm by the bound above.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- The orthonormal basis. -/
abbrev obasis (d : ℕ) : OrthonormalBasis (Fin d) ℝ (EuclSpace d) :=
  EuclideanSpace.basisFun (Fin d) ℝ

/-- The coordinate functional. -/
def coordF (i : Fin d) : EuclSpace d →L[ℝ] ℝ :=
  InnerProductSpace.toDual ℝ (EuclSpace d) (obasis d i)

theorem coordF_apply (i : Fin d) (u : EuclSpace d) :
    coordF i u = inner ℝ (obasis d i) u := by
  simp [coordF]

/-- **The form of a matrix.** -/
def formOfMatrix (A : Fin d → Fin d → ℝ) : Bilin d :=
  ∑ i, ∑ j, A i j • (coordF i).smulRight (coordF j)

set_option synthInstance.maxHeartbeats 400000 in
-- Sums and scalar multiples of forms, applied twice.
theorem formOfMatrix_apply (A : Fin d → Fin d → ℝ) (u w : EuclSpace d) :
    (formOfMatrix A u) w
      = ∑ i, ∑ j, A i j * (inner ℝ (obasis d i) u * inner ℝ (obasis d j) w) := by
  simp only [formOfMatrix, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    coordF_apply, smul_eq_mul]

set_option synthInstance.maxHeartbeats 400000 in
-- As above.
theorem form_sub_apply (X Y : Bilin d) (u w : EuclSpace d) :
    ((X - Y) u) w = (X u) w - (Y u) w := by
  simp only [sub_apply]

set_option synthInstance.maxHeartbeats 400000 in
-- Linearity of a form in both arguments, over finite sums.
/-- **The basis expansion of a form.** -/
theorem form_expand (Z : Bilin d) (u w : EuclSpace d) :
    (Z u) w = ∑ i, ∑ j, inner ℝ (obasis d i) u * inner ℝ (obasis d j) w
      * (Z (obasis d i)) (obasis d j) := by
  have hu := (obasis d).sum_repr' u
  have hw := (obasis d).sum_repr' w
  calc (Z u) w
      = (Z (∑ i, inner ℝ (obasis d i) u • obasis d i))
          (∑ j, inner ℝ (obasis d j) w • obasis d j) := by rw [hu, hw]
    _ = ∑ i, ∑ j, inner ℝ (obasis d i) u * inner ℝ (obasis d j) w
          * (Z (obasis d i)) (obasis d j) := by
        simp only [map_sum, map_smul, sum_apply, smul_apply, smul_eq_mul,
          Finset.mul_sum, mul_assoc]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- A coordinate is bounded by the norm. -/
theorem abs_coord_le (i : Fin d) (u : EuclSpace d) :
    |inner ℝ (obasis d i) u| ≤ ‖u‖ := by
  have h := abs_real_inner_le_norm (obasis d i) u
  rw [(obasis d).orthonormal.1 i, one_mul] at h
  exact h

/-- **The norm of a form is bounded by the sum of its entries.** -/
theorem norm_form_le_sum (Z : Bilin d) :
    ‖Z‖ ≤ ∑ i, ∑ j, |(Z (obasis d i)) (obasis d j)| := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro u w
  have key : |(Z u) w|
      ≤ ∑ i, ∑ j, ‖u‖ * ‖w‖ * |(Z (obasis d i)) (obasis d j)| := by
    rw [form_expand Z u w]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_mul]
    have h1 := abs_coord_le i u
    have h2 := abs_coord_le j w
    have h12 : |inner ℝ (obasis d i) u| * |inner ℝ (obasis d j) w| ≤ ‖u‖ * ‖w‖ :=
      mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    exact mul_le_mul_of_nonneg_right h12 (abs_nonneg _)
  have e : ∑ i, ∑ j, ‖u‖ * ‖w‖ * |(Z (obasis d i)) (obasis d j)|
      = (∑ i, ∑ j, |(Z (obasis d i)) (obasis d j)|) * ‖u‖ * ‖w‖ := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [Real.norm_eq_abs, ← e]
  exact key

/-- **The form of a matrix has that matrix.** -/
theorem formOfMatrix_basis (A : Fin d → Fin d → ℝ) (k l : Fin d) :
    (formOfMatrix A (obasis d k)) (obasis d l) = A k l := by
  have ho := orthonormal_iff_ite.1 (obasis d).orthonormal
  rw [formOfMatrix_apply]
  simp only [ho]
  simp

/-- **A sequence of forms with bounded entries has a subsequence converging in
operator norm.** -/
theorem exists_subseq_form (Xs : ℕ → Bilin d) {L : ℝ}
    (hL : ∀ n i j, |(Xs n (obasis d i)) (obasis d j)| ≤ L) :
    ∃ X : Bilin d, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => ‖Xs (φ n) - X‖) atTop (𝓝 0) := by
  set R := max L 0 with hR
  have hR0 : 0 ≤ R := le_max_right _ _
  set A : ℕ → Fin d → Fin d → ℝ := fun n i j => (Xs n (obasis d i)) (obasis d j)
    with hAdef
  have hA : ∀ n, A n ∈ closedBall (0 : Fin d → Fin d → ℝ) R := by
    intro n
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0]
    intro i
    rw [pi_norm_le_iff_of_nonneg hR0]
    intro j
    rw [Real.norm_eq_abs]
    exact (hL n i j).trans (le_max_left _ _)
  obtain ⟨Ainf, _, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded isBounded_closedBall hA
  refine ⟨formOfMatrix Ainf, φ, hφ, ?_⟩
  -- each entry converges
  have hentry : ∀ i j, Tendsto (fun n => ‖A (φ n) i j - Ainf i j‖) atTop (𝓝 0) := by
    intro i j
    have hcont : Continuous (fun B : Fin d → Fin d → ℝ => B i j) :=
      (continuous_apply j).comp (continuous_apply i)
    have hc : Tendsto (fun n => A (φ n) i j) atTop (𝓝 (Ainf i j)) :=
      (hcont.tendsto Ainf).comp hlim
    exact tendsto_iff_norm_sub_tendsto_zero.1 hc
  have hsum : Tendsto (fun n => ∑ i, ∑ j, ‖A (φ n) i j - Ainf i j‖) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun i _ =>
      tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun j _ => hentry i j
    simpa using this
  -- the norm is bounded by the entries
  refine squeeze_zero (fun n => ContinuousLinearMap.opNorm_nonneg _) (fun n => ?_) hsum
  refine (norm_form_le_sum _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [form_sub_apply, formOfMatrix_basis, Real.norm_eq_abs]

end

end PLaplacian
