/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Radius

@[expose] public section

/-!
# The average of a quadratic form over a ball

The average of X z z over a centred ball of radius epsilon is epsilon squared
over d plus two, times the trace. This is the theorem the moment computations
of Plaplacian.BallMoments were built for, and it is the analytic core of the
asymptotic expansion of the step operator.

The proof expands the quadratic form in coordinates, exchanges the resulting
double sum with the average, kills the off-diagonal terms by the vanishing
mixed moments, and evaluates the diagonal terms by the second moment at radius
epsilon. The surviving sum is the trace.

## Set-average lemmas absent from Mathlib

Two were needed and are proved here. Mathlib has integral_mul_const but no
set-average analogue, and setAverage_add but no finite-sum version. With
setAverage_mono, proved in Plaplacian.Average, that is three omissions from
the same corner of the library: the set-average API is visibly thinner than
the integral API it is built on.

## Main results

- quadratic_expand: coordinate expansion of a bilinear form.
- setAverage_mul_const, setAverage_finsetSum: the missing API.
- setAverage_quadratic: the theorem.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## Coordinate expansion of a bilinear form -/

theorem sum_single_eq (z : EuclSpace d) :
    ∑ i : Fin d, (z.ofLp i) • EuclideanSpace.single i (1:ℝ) = z := by
  have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr z
  simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using h

theorem bilinear_expand_left (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ)
    (z w : EuclSpace d) :
    X z w = ∑ i : Fin d,
      (z.ofLp i) * X (EuclideanSpace.single i (1:ℝ)) w := by
  conv_lhs => rw [← sum_single_eq z]
  rw [map_sum]; simp

theorem bilinear_expand_right (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ)
    (v w : EuclSpace d) :
    X v w = ∑ j : Fin d,
      (w.ofLp j) * X v (EuclideanSpace.single j (1:ℝ)) := by
  conv_lhs => rw [← sum_single_eq w]
  rw [map_sum]; simp

theorem quadratic_expand (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ)
    (z : EuclSpace d) :
    X z z = ∑ i : Fin d, ∑ j : Fin d,
      (z.ofLp i) * (z.ofLp j)
        * X (EuclideanSpace.single i (1:ℝ))
            (EuclideanSpace.single j (1:ℝ)) := by
  rw [bilinear_expand_left X z z]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bilinear_expand_right X (EuclideanSpace.single i (1:ℝ)) z,
      Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-! ## Set-average lemmas absent from Mathlib -/

/-- Mathlib has `integral_mul_const` but no set-average analogue. -/
theorem setAverage_mul_const (f : EuclSpace d → ℝ) (c : ℝ)
    (s : Set (EuclSpace d)) :
    (⨍ z in s, f z * c) = (⨍ z in s, f z) * c := by
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq,
      MeasureTheory.integral_mul_const, smul_eq_mul, smul_eq_mul]
  ring

/-- Mathlib has `setAverage_add` but no finite-sum version. -/
theorem setAverage_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → EuclSpace d → ℝ) (t : Set (EuclSpace d))
    (hf : ∀ i ∈ s, MeasureTheory.IntegrableOn (f i) t) :
    (⨍ z in t, ∑ i ∈ s, f i z) = ∑ i ∈ s, ⨍ z in t, f i z := by
  simp only [MeasureTheory.setAverage_eq, smul_eq_mul]
  rw [MeasureTheory.integral_finsetSum s hf, Finset.mul_sum]

/-! ## Per-term averages -/

theorem setAverage_mul_coord_eq_zero (i j : Fin d) (hij : i ≠ j) {ε : ℝ} :
    (⨍ z in ball (0 : EuclSpace d) ε, (z.ofLp i) * (z.ofLp j)) = 0 := by
  rw [MeasureTheory.setAverage_eq, integral_mul_coord_ball_eq_zero i j hij ε]
  simp

theorem setAverage_mul_coord_diag [Nontrivial (EuclSpace d)] (hd : 0 < d)
    (i : Fin d) {ε : ℝ} (hε : 0 < ε) :
    (⨍ z in ball (0 : EuclSpace d) ε, (z.ofLp i) * (z.ofLp i))
      = ε ^ 2 / ((d : ℝ) + 2) := by
  have h : (fun z : EuclSpace d => (z.ofLp i) * (z.ofLp i))
      = fun z : EuclSpace d => (z.ofLp i) ^ 2 := by
    funext z; ring
  rw [h]
  exact Radius.setAverage_sq_coord_ball_eps hd i hε

theorem setAverage_term [Nontrivial (EuclSpace d)] (hd : 0 < d)
    (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) (i j : Fin d) {ε : ℝ}
    (hε : 0 < ε) :
    (⨍ z in ball (0 : EuclSpace d) ε, (z.ofLp i) * (z.ofLp j)
        * X (EuclideanSpace.single i (1:ℝ)) (EuclideanSpace.single j (1:ℝ)))
      = (if i = j then ε ^ 2 / ((d : ℝ) + 2) else 0)
        * X (EuclideanSpace.single i (1:ℝ))
            (EuclideanSpace.single j (1:ℝ)) := by
  rw [setAverage_mul_const (fun z => (z.ofLp i) * (z.ofLp j))]
  by_cases h : i = j
  · subst h
    rw [ite_eq_left rfl, setAverage_mul_coord_diag hd i hε]
  · rw [ite_eq_right h, setAverage_mul_coord_eq_zero i j h]

theorem inner_sum_collapse (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ)
    (i : Fin d) {ε : ℝ} :
    (∑ j : Fin d, (if i = j then ε ^ 2 / ((d : ℝ) + 2) else 0)
        * X (EuclideanSpace.single i (1:ℝ))
            (EuclideanSpace.single j (1:ℝ)))
      = ε ^ 2 / ((d : ℝ) + 2)
        * X (EuclideanSpace.single i (1:ℝ))
            (EuclideanSpace.single i (1:ℝ)) := by
  rw [Finset.sum_congr rfl (fun j _ => ite_mul _ _ _ _)]
  simp

/-! ## Integrability -/

theorem integrableOn_term (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ)
    (i j : Fin d) (ε : ℝ) :
    MeasureTheory.IntegrableOn
      (fun z : EuclSpace d => (z.ofLp i) * (z.ofLp j)
        * X (EuclideanSpace.single i (1:ℝ)) (EuclideanSpace.single j (1:ℝ)))
      (ball (0 : EuclSpace d) ε) :=
  (ContinuousOn.integrableOn_compact (isCompact_closedBall _ _)
    (by fun_prop)).mono_set ball_subset_closedBall

theorem integrableOn_inner_sum (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ)
    (i : Fin d) (ε : ℝ) :
    MeasureTheory.IntegrableOn
      (fun z : EuclSpace d => ∑ j : Fin d, (z.ofLp i) * (z.ofLp j)
        * X (EuclideanSpace.single i (1:ℝ)) (EuclideanSpace.single j (1:ℝ)))
      (ball (0 : EuclSpace d) ε) :=
  MeasureTheory.integrable_finsetSum _ fun j _ => integrableOn_term X i j ε

/-! ## The quadratic average -/

/-- **The average of a quadratic form over a centred ball.**

The theorem the moment computations of `Plaplacian.BallMoments` were built
for: the average of `X z z` over a ball of radius `ε` is `ε² / (d+2)` times
the trace. -/
theorem setAverage_quadratic [Nontrivial (EuclSpace d)] (hd : 0 < d)
    (X : EuclSpace d →L[ℝ] EuclSpace d →L[ℝ] ℝ) {ε : ℝ} (hε : 0 < ε) :
    (⨍ z in ball (0 : EuclSpace d) ε, X z z)
      = ε ^ 2 / ((d : ℝ) + 2) * laplacianOf X := by
  have hexp : (⨍ z in ball (0 : EuclSpace d) ε, X z z)
      = ⨍ z in ball (0 : EuclSpace d) ε,
          ∑ i : Fin d, ∑ j : Fin d, (z.ofLp i) * (z.ofLp j)
            * X (EuclideanSpace.single i (1:ℝ))
                (EuclideanSpace.single j (1:ℝ)) := by
    congr 1
    funext z
    exact quadratic_expand X z
  rw [hexp]
  rw [setAverage_finsetSum Finset.univ _ _
      (fun i _ => integrableOn_inner_sum X i ε)]
  have hstep : ∀ i : Fin d,
      (⨍ z in ball (0 : EuclSpace d) ε, ∑ j : Fin d, (z.ofLp i) * (z.ofLp j)
          * X (EuclideanSpace.single i (1:ℝ))
              (EuclideanSpace.single j (1:ℝ)))
        = ε ^ 2 / ((d : ℝ) + 2)
          * X (EuclideanSpace.single i (1:ℝ))
              (EuclideanSpace.single i (1:ℝ)) := by
    intro i
    rw [setAverage_finsetSum Finset.univ _ _
        (fun j _ => integrableOn_term X i j ε)]
    rw [Finset.sum_congr rfl (fun j _ => setAverage_term hd X i j hε)]
    exact inner_sum_collapse X i
  rw [Finset.sum_congr rfl (fun i _ => hstep i)]
  unfold laplacianOf
  rw [Finset.mul_sum]

end

end PLaplacian
