/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.ExtErrRate

@[expose] public section

/-!
# The weighted error

For p at least two the two weights of the operator are each at most one in
absolute value, so the weighted combination of the two error halves is bounded
by the sum of their absolute values. The weights do not amplify.

That is what makes a rate meaningful. Bounding the error by itself divided by
epsilon squared, times epsilon squared, is true of any quantity and says
nothing; the content is that a rate for each half yields a rate for the total
with no new dependence on epsilon introduced.

## Main results

- abs_alpha_le_one, abs_beta_le_one
- weighted_error_le
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## The expansion with a genuine rate

The error must be bounded by a constant times a power of `ε` above two, with
the constant independent of `ε`. Bolting a bound on afterwards is vacuous: any
quantity is bounded by itself over `ε²` times `ε²`.

The content is therefore a restatement of the expansion carrying the bounds
through. The two halves enter weighted by `α` and `β`, both at most one in
absolute value for `2 ≤ p`, so

  `|E| ≤ |e₁| + |e₂|`

where `e₁` is the extreme-value error and `e₂` the average error. The average
error is at most `K ε³` by `setAverage_taylorErr_le`. The extreme-value error
is bounded by the sandwich width, which the localization puts at order
`ε^{5/2}`.
-/

/-- The weights are bounded by one for `2 ≤ p`. -/
theorem abs_alpha_le_one (p : ℝ) (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ)) :
    |(p - 2) / (p + (d : ℝ))| ≤ 1 := by
  rw [abs_div, abs_of_nonneg (by linarith : (0:ℝ) ≤ p - 2),
      abs_of_pos hpd, div_le_one hpd]
  have hd : (0:ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  linarith

theorem abs_beta_le_one (p : ℝ) (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ)) :
    |((d : ℝ) + 2) / (p + (d : ℝ))| ≤ 1 := by
  have hd2 : (0:ℝ) < (d : ℝ) + 2 := by positivity
  rw [abs_div, abs_of_pos hd2, abs_of_pos hpd, div_le_one hpd]
  linarith

/-- **The weighted error, bounded by the sum of the halves.**

This is the step that makes the rate meaningful: the weights do not amplify,
so a rate for each half gives a rate for the total, with the same constant
structure and no dependence on `ε` beyond the halves' own. -/
theorem weighted_error_le (p : ℝ) (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    (e₁ e₂ : ℝ) :
    |(p - 2) / (p + (d : ℝ)) * e₁
        + ((d : ℝ) + 2) / (p + (d : ℝ)) * e₂|
      ≤ |e₁| + |e₂| := by
  have ha := abs_alpha_le_one (d := d) p hp hpd
  have hb := abs_beta_le_one (d := d) p hp hpd
  calc |(p - 2) / (p + (d : ℝ)) * e₁
          + ((d : ℝ) + 2) / (p + (d : ℝ)) * e₂|
      ≤ |(p - 2) / (p + (d : ℝ)) * e₁|
        + |((d : ℝ) + 2) / (p + (d : ℝ)) * e₂| := abs_add_le _ _
    _ = |(p - 2) / (p + (d : ℝ))| * |e₁|
        + |((d : ℝ) + 2) / (p + (d : ℝ))| * |e₂| := by
          rw [abs_mul, abs_mul]
    _ ≤ 1 * |e₁| + 1 * |e₂| := by
          have h1 : (0:ℝ) ≤ |e₁| := abs_nonneg e₁
          have h2 : (0:ℝ) ≤ |e₂| := abs_nonneg e₂
          nlinarith [ha, hb, h1, h2]
    _ = |e₁| + |e₂| := by ring

end

end PLaplacian
