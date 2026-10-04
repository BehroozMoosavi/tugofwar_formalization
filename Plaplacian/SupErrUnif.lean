/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.LocDistUnif

/-!
# The supremum upper error, uniformly

At the shared maximizer the upper bound carries a comparison term and a Taylor
error. The comparison term is a product of three factors --- the Hessian norm,
the localization distance and the sum of the increment norms --- each bounded
uniformly, so it is at most the Hessian bound times the parameter times the
square root of the uniform localization bound. The Taylor error is at most the
uniform cubic constant times the cube of the parameter.

So the supremum exceeds its expansion by a quantity free of the base point and
of order the parameter to the five halves. This is the upper half of the
extreme-value error made uniform, and it composes the bound at the maximizer
with the uniform localization because the two now share their witness.

## Main results

- sup_err_le
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The supremum's upper error, uniformly

At the shared maximizer the upper bound carries a comparison term and a Taylor
error. The comparison term is the Hessian norm times the localization distance
times the sum of the increments' norms; with each factor bounded uniformly ---
the Hessian by `H`, the distance by `√U`, the sum by `2ε` --- it is at most
`H ε √U`. The Taylor error is at most `K ε³`.

So the supremum exceeds its expansion by at most `H ε √U + K ε³`, a quantity
free of the base point and of order `ε^{5/2}`.

The uniform Taylor bound and constants are hypotheses, so that this step is
the arithmetic of the composition and the extraction of the constants is
separate.
-/


/-- **The supremum's upper error, uniformly.** -/
theorem sup_err_le {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ)
    {x : EuclSpace d} (hx : gradient φ x ≠ 0) {ε K H g : ℝ}
    (hε : 0 < ε) (hK : 0 ≤ K)
    (hTerr : ∀ z : EuclSpace d, ‖z‖ ≤ ε → |taylorErr φ x z| ≤ K * ε ^ 3)
    (hH : ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ H) (hg : 0 < g)
    (hgx : g ≤ ‖gradient φ x‖) :
    sSup (φ '' closedBall x ε)
        - (φ x + ε * ‖gradient φ x‖
            + ε ^ 2 / 2 * infLaplacianOf (gradient φ x)
                (fderiv ℝ (fderiv ℝ φ) x))
      ≤ H * ε * Real.sqrt (2 * ε * ((H * ε ^ 2 + 2 * K * ε ^ 3) / g))
        + K * ε ^ 3 := by
  obtain ⟨y, hyMem, _hsup, hdom, hbound⟩ := sup_upper_at_max hφ hx hε
  have hyb : ‖y - x‖ ≤ ε := norm_sub_le_of_mem hyMem
  have hshift : ‖ε • gradDir φ x‖ = ε := norm_eps_gradDir hx hε
  have hTy := hTerr (y - x) hyb
  have hTs := hTerr (ε • gradDir φ x) (le_of_eq hshift)
  -- the localization distance, uniformly
  have hD := loc_dist_unif hx hε hK hyb hdom hTy hTs hH hg hgx
  set U := 2 * ε * ((H * ε ^ 2 + 2 * K * ε ^ 3) / g) with hU
  -- the factors and their bounds
  have hHnn : (0:ℝ) ≤ H :=
    le_trans (ContinuousLinearMap.opNorm_nonneg _) hH
  have hsum : ‖y - x‖ + ‖ε • gradDir φ x‖ ≤ 2 * ε := by
    rw [hshift]; linarith [hyb]
  have hsumnn : (0:ℝ) ≤ ‖y - x‖ + ‖ε • gradDir φ x‖ := by positivity
  have hsqnn : (0:ℝ) ≤ Real.sqrt U := Real.sqrt_nonneg U
  -- the comparison term
  have hAB : ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖y - x - ε • gradDir φ x‖
      ≤ H * Real.sqrt U :=
    mul_le_mul hH hD (norm_nonneg _) hHnn
  have hABC : ‖fderiv ℝ (fderiv ℝ φ) x‖ * ‖y - x - ε • gradDir φ x‖
        * (‖y - x‖ + ‖ε • gradDir φ x‖)
      ≤ H * Real.sqrt U * (2 * ε) :=
    mul_le_mul hAB hsum hsumnn (mul_nonneg hHnn hsqnn)
  have hcomp : (1 / 2) * (‖fderiv ℝ (fderiv ℝ φ) x‖
        * ‖y - x - ε • gradDir φ x‖ * (‖y - x‖ + ‖ε • gradDir φ x‖))
      ≤ H * ε * Real.sqrt U := by
    nlinarith [hABC]
  -- the Taylor error at the maximizer
  have hTy' := (abs_le.1 hTy).2
  linarith [hbound, hcomp, hTy']

end

end PLaplacian
