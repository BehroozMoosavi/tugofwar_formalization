import Mathlib

open MeasureTheory Metric Set

example (d : ℕ) (i : Fin d) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin d)) 1, (-z) i)
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin d)) 1, z i := by
  have hneg : (volume : Measure (EuclideanSpace ℝ (Fin d))).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular volume
  rw [← integral_indicator measurableSet_ball,
      ← integral_indicator measurableSet_ball]
  rw [← integral_neg_eq_self (fun z => (ball (0 : EuclideanSpace ℝ (Fin d)) 1).indicator (fun w => w i) z) volume]
  congr 1
  ext z
  simp only [indicator_apply]
  by_cases h : z ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1
  · simp [h, show (-z) ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 from by simpa using h]
  · simp [h, show (-z) ∉ ball (0 : EuclideanSpace ℝ (Fin d)) 1 from by simpa using h]
