/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.ExpUnif

@[expose] public section

/-!
# The uniform error is small against the squared parameter

The uniform bound on the expansion error is the squared parameter times a
factor that is continuous and vanishes at zero, so the error is eventually
below any positive multiple of the squared parameter.

## Main results

- errFactor, tendsto_errFactor
- bound_eq_sq_mul
- eventually_bound_le
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The uniform error is small against the squared parameter

The uniform bound on the expansion error factors as the squared parameter
times

  `q ε = H √(2ε(H + 2Kε)/g) + (K + Ka) ε`,

for positive parameter. That factor is continuous and vanishes at zero, so it
is eventually below any positive bound, and the error is eventually below that
bound times the squared parameter.

The factorisation uses `√(ε² X) = ε √X` for nonnegative parameter, which is
where the square root's argument is reorganised to expose the squared
parameter.
-/

/-- The factor, continuous and vanishing at zero. -/
def errFactor (H K Ka g ε : ℝ) : ℝ :=
  H * Real.sqrt (2 * ε * (H + 2 * K * ε) / g) + (K + Ka) * ε

/-- It tends to zero as the parameter does. -/
theorem tendsto_errFactor (H K Ka g : ℝ) :
    Filter.Tendsto (errFactor H K Ka g) (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds 0) := by
  have hcont : Continuous (errFactor H K Ka g) := by
    unfold errFactor; fun_prop
  have h0 : errFactor H K Ka g 0 = 0 := by
    unfold errFactor; simp
  have h := hcont.tendsto 0
  rw [h0] at h
  exact h.mono_left nhdsWithin_le_nhds

/-- **The factorisation.** For positive parameter, the uniform bound is the
squared parameter times the factor. -/
theorem bound_eq_sq_mul {H K Ka g ε : ℝ} (hε : 0 < ε) :
    (H * ε * Real.sqrt (2 * ε * ((H * ε ^ 2 + 2 * K * ε ^ 3) / g))
        + K * ε ^ 3) + Ka * ε ^ 3
      = ε ^ 2 * errFactor H K Ka g ε := by
  have hinner : 2 * ε * ((H * ε ^ 2 + 2 * K * ε ^ 3) / g)
      = ε ^ 2 * (2 * ε * (H + 2 * K * ε) / g) := by ring
  rw [hinner, Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq (le_of_lt hε)]
  unfold errFactor
  ring

/-- **The error is eventually small against the squared parameter.** -/
theorem eventually_bound_le {H K Ka g η : ℝ} (hη : 0 < η) :
    ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (H * ε * Real.sqrt (2 * ε * ((H * ε ^ 2 + 2 * K * ε ^ 3) / g))
          + K * ε ^ 3) + Ka * ε ^ 3 ≤ η * ε ^ 2 := by
  have hlt : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      errFactor H K Ka g ε < η :=
    (tendsto_errFactor H K Ka g).eventually (eventually_lt_nhds hη)
  have hpos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
    self_mem_nhdsWithin
  filter_upwards [hlt, hpos] with ε hq hε
  rw [bound_eq_sq_mul hε]
  have hε2 : (0:ℝ) ≤ ε ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left (le_of_lt hq) hε2
  linarith [this]

end

end PLaplacian
