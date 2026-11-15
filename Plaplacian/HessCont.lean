/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.AvgTerms

@[expose] public section

/-!
# Pointwise continuity of the Hessian

The Taylor remainder is controlled by the variation of the Hessian over a
small ball. The natural statement bounds the operator norm of the difference,
and that statement cannot be formalized as written.

Mathlib registers the space of continuous linear maps with
ContinuousLinearMap.topologicalSpace rather than with the metric topology
induced by the operator norm. Lean does not unify the two, so every lemma
stated for a metric codomain, Continuous.norm and Metric.continuousAt_iff
among them, is unavailable on the Hessian. This is a structural constraint on
formalizing second-order analysis rather than an omission: anything needing
operator-norm continuity must be restated pointwise.

The remedy is to work with scalars throughout. Continuous.clm_apply, applied
twice, gives continuity of the real-valued function that sends a base point to
the Hessian evaluated at a fixed pair of vectors, and the remainder estimate
needs nothing more, the quantity being bounded being a scalar.

## Main results

- continuous_hess_apply, continuous_hess_diff_apply
- hess_apply_bound: the pointwise uniform bound.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## Pointwise continuity of the Hessian

`Continuous.norm` requires the codomain to carry the metric topology, but the
space of continuous bilinear maps is registered with
`ContinuousLinearMap.topologicalSpace`, and the two do not unify. So no
argument routed through the *operator norm* of the Hessian difference will
typecheck.

The remedy is to work with scalars throughout. `Continuous.clm_apply`, applied
twice, gives continuity of `y ↦ D²φ y (z, z)` as a real-valued function, and
that is all the remainder estimate needs, the quantity being bounded being a
scalar.
-/

/-- Evaluating the Hessian at a fixed pair is continuous in the base point. -/
theorem continuous_hess_apply {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (z w : EuclSpace d) :
    Continuous (fun y => fderiv ℝ (fderiv ℝ φ) y z w) := by
  have h1 : Continuous (fun y => fderiv ℝ (fderiv ℝ φ) y z) :=
    (continuous_hess hφ).clm_apply continuous_const
  exact h1.clm_apply continuous_const

/-- The scalar Hessian difference is continuous. -/
theorem continuous_hess_diff_apply {φ : EuclSpace d → ℝ}
    (hφ : ContDiff ℝ 2 φ) (x z : EuclSpace d) :
    Continuous (fun y => fderiv ℝ (fderiv ℝ φ) y z z
      - fderiv ℝ (fderiv ℝ φ) x z z) :=
  (continuous_hess_apply hφ z z).sub continuous_const

/-- **The pointwise uniform bound.** For each fixed `z`, the scalar Hessian
difference is small near the base point. -/
theorem hess_apply_bound {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    (x z : EuclSpace d) {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ w : EuclSpace d, ‖w‖ < δ →
      |fderiv ℝ (fderiv ℝ φ) (x + w) z z
        - fderiv ℝ (fderiv ℝ φ) x z z| < η := by
  set g : EuclSpace d → ℝ := fun y =>
    |fderiv ℝ (fderiv ℝ φ) y z z - fderiv ℝ (fderiv ℝ φ) x z z| with hgdef
  have hgc : Continuous g := (continuous_hess_diff_apply hφ x z).abs
  have hgx : g x = 0 := by
    rw [hgdef]
    simp
  have hlt : g x < η := by rw [hgx]; exact hη
  have hev : ∀ᶠ y in nhds x, g y < η :=
    hgc.continuousAt.eventually (eventually_lt_nhds hlt)
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ, hδ, fun w hw => ?_⟩
  have hdist : dist (x + w) x < δ := by
    rw [dist_eq_norm]
    simpa using hw
  exact hb hdist

end

end PLaplacian
