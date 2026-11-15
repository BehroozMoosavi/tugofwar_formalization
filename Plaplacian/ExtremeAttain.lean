/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.AvgExpansion

@[expose] public section

/-!
# Attainment of the extreme values

The extreme-value half of the asymptotic expansion needs the supremum and
infimum of a test function over a closed ball to be attained. Compactness
gives this, and IsCompact.exists_sSup_image_eq gives the stronger form in
which the supremum equals the value at a point of the ball, which is what the
computation needs. The IsMaxOn form is also recorded, since the localization
argument uses it.

Also here: the two shifted points, at plus and minus epsilon times a unit
vector from the centre, both of which lie in the closed ball.

## Main results

- exists_sSup_closedBall, exists_sInf_closedBall
- exists_isMaxOn_closedBall, exists_isMinOn_closedBall
- mem_closedBall_shift, mem_closedBall_shift_neg
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## Attainment of the extreme values

The extreme-value expansion needs the supremum and infimum over the closed
ball to be attained, and `IsCompact.exists_sSup_image_eq` gives the stronger
statement that the supremum *equals* the value at a point of the ball.
-/

theorem nonempty_closedBall' (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    (closedBall x ε).Nonempty :=
  ⟨x, mem_closedBall_self hε.le⟩

/-- **The supremum over a closed ball is attained.** -/
theorem exists_sSup_closedBall {φ : EuclSpace d → ℝ} (hφ : Continuous φ)
    (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ closedBall x ε, sSup (φ '' closedBall x ε) = φ y :=
  (isCompact_closedBall x ε).exists_sSup_image_eq
    (nonempty_closedBall' x hε) hφ.continuousOn

/-- **And the infimum.** -/
theorem exists_sInf_closedBall {φ : EuclSpace d → ℝ} (hφ : Continuous φ)
    (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ closedBall x ε, sInf (φ '' closedBall x ε) = φ y :=
  (isCompact_closedBall x ε).exists_sInf_image_eq
    (nonempty_closedBall' x hε) hφ.continuousOn

/-- The maximizer, in `IsMaxOn` form, which is what the upper bound needs. -/
theorem exists_isMaxOn_closedBall {φ : EuclSpace d → ℝ} (hφ : Continuous φ)
    (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ closedBall x ε, IsMaxOn φ (closedBall x ε) y :=
  (isCompact_closedBall x ε).exists_isMaxOn
    (nonempty_closedBall' x hε) hφ.continuousOn

theorem exists_isMinOn_closedBall {φ : EuclSpace d → ℝ} (hφ : Continuous φ)
    (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ closedBall x ε, IsMinOn φ (closedBall x ε) y :=
  (isCompact_closedBall x ε).exists_isMinOn
    (nonempty_closedBall' x hε) hφ.continuousOn

/-! ### The shifted point -/

/-- `x + ε ν` lies in the closed ball, for a unit vector `ν`. -/
theorem mem_closedBall_shift (x : EuclSpace d) {ν : EuclSpace d}
    (hν : ‖ν‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    x + ε • ν ∈ closedBall x ε := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h : x + ε • ν - x = ε • ν := by abel
  rw [h, norm_smul, hν, Real.norm_eq_abs, abs_of_pos hε, mul_one]

/-- And so does `x - ε ν`. -/
theorem mem_closedBall_shift_neg (x : EuclSpace d) {ν : EuclSpace d}
    (hν : ‖ν‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    x - ε • ν ∈ closedBall x ε := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  have h : x - ε • ν - x = -(ε • ν) := by abel
  rw [h, norm_neg, norm_smul, hν, Real.norm_eq_abs, abs_of_pos hε, mul_one]

end

end PLaplacian
