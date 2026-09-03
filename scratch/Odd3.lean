import Mathlib

open MeasureTheory Metric Set

#check @Metric.mem_ball_zero_iff
#check @norm_neg
#check @MeasureTheory.Measure.measure_preimage_neg
#check @Set.neg_mem_ball_zero
#check @MeasureTheory.Measure.restrict_map
#check @MeasureTheory.MeasurePreserving.setIntegral_image_emb
#check @MeasureTheory.integral_neg

example (d : ℕ) (z : EuclideanSpace ℝ (Fin d)) :
    (-z) ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 ↔ z ∈ ball 0 1 := by
  simp [mem_ball_zero_iff]

example (d : ℕ) : -(ball (0 : EuclideanSpace ℝ (Fin d)) 1) = ball 0 1 := by
  ext z
  simp [mem_neg, mem_ball_zero_iff]

example (d : ℕ) (i : Fin d) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin d)) 1, (-z) i)
      = -∫ z in ball (0 : EuclideanSpace ℝ (Fin d)) 1, z i := by
  simp [PiLp.neg_apply]
