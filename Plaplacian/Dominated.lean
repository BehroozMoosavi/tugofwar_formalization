/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Plaplacian.IndexSelection

/-!
# Dominated convergence for the deficit

This file proves step (2.7) of the uniform convergence argument in
Luiro--Parviainen--Saksman, Differential Integral Equations 27 (2014),
Theorem 2.1: for a sequence bounded by a constant and converging pointwise to
zero, the integrals over a set of finite measure tend to zero.

Mathlib has no set-integral form of dominated convergence, so the whole-space
version is applied to the restricted measure, a set integral being by
definition an integral against volume.restrict S.

## Main results

- tendsto_setIntegral_deficit
-/

open MeasureTheory Metric Set Filter

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-- **LPS's (2.7).** For a sequence of functions bounded by a constant and
converging pointwise to zero, the integrals over a finite-measure set tend to
zero. Applied to the restricted measure, since a set integral is an integral
against `volume.restrict S`. -/
theorem tendsto_setIntegral_deficit {S : Set (EuclSpace d)}
    (hSfin : volume S ≠ ⊤)
    {u : EuclSpace d → ℝ} {w : ℕ → EuclSpace d → ℝ} {C : ℝ}
    (hmeas : ∀ j, Measurable (fun x => u x - w j x))
    (hC : ∀ j x, |u x - w j x| ≤ C)
    (hconv : ∀ x, Tendsto (fun j => w j x) atTop (nhds (u x))) :
    Tendsto (fun j => ∫ x in S, (u x - w j x)) atTop (nhds 0) := by
  have hbound : Integrable (fun _ : EuclSpace d => C)
      (volume.restrict S) := by
    refine integrable_const_iff.2 (Or.inr ?_)
    constructor
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_ne le_top hSfin
  have hzero : (0 : ℝ) = ∫ x, (0 : ℝ) ∂(volume.restrict S) := by simp
  rw [hzero]
  exact MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun _ => C)
    (fun j => (hmeas j).aestronglyMeasurable)
    hbound
    (fun j => Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hC j x)
    (Filter.Eventually.of_forall fun x => by
      have h := (hconv x).const_sub (u x)
      simpa using h)

end

end PLaplacian
