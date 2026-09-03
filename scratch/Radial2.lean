import Mathlib

open MeasureTheory Metric

#check @MeasureTheory.integral_fun_norm_addHaar
#check @MeasureTheory.Measure.IsNegInvariant
#check @MeasureTheory.integral_neg_eq_self
#check @polarCoord
#check @MeasureTheory.Measure.measurePreserving_neg
#check @integral_comp_neg

example (d : ℕ) (i : Fin d) :
    (∫ z in ball (0 : EuclideanSpace ℝ (Fin d)) 1, z i) = 0 := by
  apply?
