/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.Positivity

/-!
# Averages over balls

Measure-theoretic infrastructure for the set average `⨍ y in ball x ε, f y`,
needed by the discrete step operator of the normalized `p`-Laplacian.

Mathlib's `average` API requires the instances `IsFiniteMeasure μ` and
`NeZero μ`. For `volume.restrict (ball x ε)` neither is automatic, and `NeZero`
genuinely needs `0 < ε`, so it cannot be a global instance. We supply both.

Monotonicity of the real-valued set average is absent from mathlib: there is
`MeasureTheory.setLAverage_mono_ae` for the `ENNReal` lower average, and
`Real.circleAverage_mono` for circle averages, but nothing for `⨍` over a
general set. `setAverage_mono` below fills that gap and is a candidate for
upstreaming.

## Main results

- `isFiniteMeasure_restrict_ball`, `neZero_restrict_ball`: the instances.
- `setAverage_mono`: monotonicity of `⨍ x in s, f x ∂μ`, in full generality.
- `setAverage_mono_ball`, `setAverage_const_ball`: ball specialisations.
-/

open MeasureTheory Metric Set

noncomputable section

/-- The ambient Euclidean space. `abbrev`, not `def`, so instance search sees
through it. -/
abbrev EuclSpace (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

namespace PLaplacian

/-- The measure of a ball of positive radius is nonzero. -/
lemma measure_ball_ne_zero (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    volume (ball x ε) ≠ 0 :=
  (measure_ball_pos volume x hε).ne'

/-- The restriction of Lebesgue measure to a ball is a finite measure. -/
lemma isFiniteMeasure_restrict_ball (x : EuclSpace d) (ε : ℝ) :
    IsFiniteMeasure (volume.restrict (ball x ε)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact measure_ball_lt_top

/-- The restriction of Lebesgue measure to a ball of positive radius is
nonzero. Cannot be an instance: the hypothesis `0 < ε` is essential. -/
lemma neZero_restrict_ball (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    NeZero (volume.restrict (ball x ε)) := by
  refine ⟨fun h => ?_⟩
  rw [Measure.restrict_eq_zero] at h
  exact measure_ball_ne_zero x hε h

/-- **Monotonicity of the set average.** No hypothesis on `μ s` is needed:
`setAverage_eq` is unconditional, and `(μ.real s)⁻¹` is nonnegative even when
`μ s = 0` or `μ s = ∞`, where the junk-value convention makes it `0`. -/
theorem setAverage_mono {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) {f g : α → ℝ}
    (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
    (h : ∀ x ∈ s, f x ≤ g x) :
    (⨍ x in s, f x ∂μ) ≤ ⨍ x in s, g x ∂μ := by
  have hint : (∫ x in s, f x ∂μ) ≤ ∫ x in s, g x ∂μ :=
    setIntegral_mono_on hf hg hs h
  have hnn : (0 : ℝ) ≤ (μ.real s)⁻¹ := by positivity
  rw [setAverage_eq, setAverage_eq]
  simp only [smul_eq_mul]
  exact mul_le_mul_of_nonneg_left hint hnn

/-- Monotonicity of the average over a ball. -/
theorem setAverage_mono_ball (x : EuclSpace d) {ε : ℝ}
    {f g : EuclSpace d → ℝ}
    (hf : IntegrableOn f (ball x ε)) (hg : IntegrableOn g (ball x ε))
    (h : ∀ y, f y ≤ g y) :
    (⨍ y in ball x ε, f y) ≤ ⨍ y in ball x ε, g y :=
  setAverage_mono measurableSet_ball hf hg (fun y _ => h y)

/-- The average of a constant over a ball of positive radius. -/
theorem setAverage_const_ball (c : ℝ) (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    (⨍ _y in ball x ε, c) = c := by
  have := isFiniteMeasure_restrict_ball x ε
  have := neZero_restrict_ball x hε
  exact average_const (volume.restrict (ball x ε)) c

end PLaplacian
