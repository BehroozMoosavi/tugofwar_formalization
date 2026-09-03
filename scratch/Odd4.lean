import Mathlib

open MeasureTheory Metric Set

example (d : ℕ) (z : EuclideanSpace ℝ (Fin d)) :
    (-z) ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ↔ z ∈ ball 0 1 := by
  simp

example (d : ℕ) : -(ball (0 : EuclideanSpace ℝ (Fin d)) 1) = ball 0 1 := by
  ext z
  simp

example (d : ℕ) (i : Fin d) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin d)) 1, (-z) i)
      = -∫ z in ball (0 : EuclideanSpace ℝ (Fin d)) 1, z i := by
  simp only [PiLp.neg_apply]
  exact integral_neg _

example (d : ℕ) (i : Fin d) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin d)) 1, (-z) i)
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin d)) 1, z i := by
  have hneg : (volume : Measure (EuclideanSpace ℝ (Fin d))).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular volume
  have hball : -(ball (0 : EuclideanSpace ℝ (Fin d)) 1) = ball 0 1 := by
    ext z; simp
  rw [← integral_indicator measurableSet_ball,
      ← integral_indicator measurableSet_ball]
  sorry
