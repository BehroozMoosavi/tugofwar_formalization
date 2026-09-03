import Mathlib

open MeasureTheory Metric Set

#check @MeasureTheory.integral_fun_norm_addHaar
#check @MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
#check @MeasureTheory.integral_indicator

example (d : ℕ) [Nontrivial (EuclideanSpace ℝ (Fin d))] :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by
  exact?

example (d : ℕ) : (volume : Measure (EuclideanSpace ℝ (Fin d))).IsNegInvariant := by
  exact?

example (d : ℕ) (i : Fin d) (z : EuclideanSpace ℝ (Fin d)) :
    (-z) i = -(z i) := by
  exact?
