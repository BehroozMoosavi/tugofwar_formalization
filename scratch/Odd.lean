import Mathlib

open MeasureTheory Metric Set

example (d : ℕ) (i : Fin d) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin d)) 1, z i) = 0 := by
  have hneg : (volume : Measure (EuclideanSpace ℝ (Fin d))).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular volume
  set I := ∫ z in ball (0 : EuclideanSpace ℝ (Fin d)) 1, z i with hI
  have key : I = -I := by
    sorry
  linarith [key]
