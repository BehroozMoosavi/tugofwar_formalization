import Mathlib

open MeasureTheory Metric

example (d : ℕ) (g : ℝ → ℝ) (hg : Continuous g) :
    ∃ c : ℝ, (∫ z in ball (0 : EuclideanSpace ℝ (Fin d)) 1, g ‖z‖)
      = c * ∫ r in (0:ℝ)..1, g r * r ^ (d - 1) := by
  exact?

example (d : ℕ) (i : Fin d) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin d)) 1, z i) = 0 := by
  exact?
