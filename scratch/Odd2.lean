import Mathlib

open MeasureTheory Metric Set

example (d : ℕ) : -(ball (0 : EuclideanSpace ℝ (Fin d)) 1) = ball 0 1 := by
  exact?

example (d : ℕ) (z : EuclideanSpace ℝ (Fin d)) :
    (-z) ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ↔ z ∈ ball 0 1 := by
  exact?

example (d : ℕ) :
    (volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (ball 0 1)
      |>.IsNegInvariant := by
  exact?

example (d : ℕ) (i : Fin d) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin d)) 1, (-z) i)
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin d)) 1, z i := by
  exact?
