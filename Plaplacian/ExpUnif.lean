/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.ExpErr

@[expose] public section

/-!
# The expansion, uniformly in the base point

The asymptotic expansion of the step operator, with its error bounded
uniformly for every base point in a ball about the maximum and every small
parameter.

Every constant is extracted once, on a single ball: a radius on which the
gradient stays above half its value at the maximum, the cubic Taylor constant
made nonnegative, the average constant, and the Hessian bound. None depends on
the base point. The quantifier order in the statement is the content, the
radius and every constant chosen before the base point and the parameter.

The informal theory states this in a phrase: the scheme is consistent locally
uniformly. Formally it took a dozen files, because each of its ingredients ---
the third-derivative bound, the Taylor error, the average error, the Hessian
norm, the gradient lower bound, the localization and the supremum and infimum
errors --- had to be made uniform separately, and two of them met the topology
obstruction of the curried derivative tower along the way.

## Main results

- expansion_uniform
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The expansion, uniformly in the base point

Every constant is extracted once, from its uniform lemma, on a single ball
about the maximum; then for every base point in that ball and every small
parameter, the hypotheses of `expansion_err_le` hold with those constants.

The constants: a radius on which the gradient stays above half its value at
the maximum, giving the lower bound `g`; the cubic Taylor constant `K` and the
average constant `Ka`, made nonnegative; and the Hessian bound `H`. None
depends on the base point, which is the whole content.

The quantifier order is explicit in the statement: the radius and every
constant are chosen before the base point and the parameter.
-/


/-- **The expansion, uniformly in the base point.** -/
theorem expansion_uniform [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ))
    {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 3 φ) {x₀ : EuclSpace d}
    (hx₀ : gradient φ x₀ ≠ 0) :
    ∃ ρ > 0, ∃ H K Ka g : ℝ, 0 < g ∧ 0 ≤ K ∧ 0 ≤ H ∧ 0 ≤ Ka ∧
      ∀ y ∈ ball x₀ ρ, ∀ ε : ℝ, 0 < ε → ε ≤ ρ →
        ∃ E : ℝ,
          tugOfWarOp p ε φ y
              = φ y + ε ^ 2 / (2 * (p + (d : ℝ)))
                  * normPLapOf p (gradient φ y)
                      (fderiv ℝ (fderiv ℝ φ) y) + E
            ∧ |E| ≤ (H * ε * Real.sqrt
                  (2 * ε * ((H * ε ^ 2 + 2 * K * ε ^ 3) / g))
                + K * ε ^ 3) + Ka * ε ^ 3 := by
  -- the radius and the gradient lower bound
  obtain ⟨ρ, hρ, hgrad⟩ := grad_lower_uniform (hφ.of_le (by norm_num)) hx₀
  set g := ‖gradient φ x₀‖ / 2 with hgdef
  have hg : 0 < g := by
    have : 0 < ‖gradient φ x₀‖ := norm_pos_iff.2 hx₀
    rw [hgdef]; linarith
  -- the uniform constants, on the closed ball of radius ρ
  obtain ⟨K₀, hK₀⟩ := taylorErr_le_cubic_uniform hφ x₀ ρ
  obtain ⟨Ka₀, hKa₀⟩ := avgErr_uniform hφ x₀ ρ
  obtain ⟨H₀, hH₀⟩ := hess_bound_uniform hφ x₀ ρ
  set H := max H₀ 0 with hHdef
  set Ka := max Ka₀ 0 with hKadef
  have hHnn : 0 ≤ H := le_max_right _ _
  have hKann : 0 ≤ Ka := le_max_right _ _
  set K := max K₀ 0 with hKdef
  have hK : 0 ≤ K := le_max_right _ _
  have hKge : K₀ ≤ K := le_max_left _ _
  refine ⟨ρ, hρ, H, K, Ka, g, hg, hK, hHnn, hKann,
    fun y hy ε hε hερ => ?_⟩
  have hyc : y ∈ closedBall x₀ ρ := ball_subset_closedBall hy
  -- the gradient at the base point
  have hgy : g < ‖gradient φ y‖ := hgrad y hy
  have hxy : gradient φ y ≠ 0 := by
    intro h; rw [h, norm_zero] at hgy; linarith
  -- the Taylor error bound at the base point
  have hTerr : ∀ z : EuclSpace d, ‖z‖ ≤ ε →
      |taylorErr φ y z| ≤ K * ε ^ 3 := by
    intro z hz
    have hzρ : ‖z‖ ≤ ρ := le_trans hz hερ
    have h1 := hK₀ y hyc z hzρ
    have hz3 : ‖z‖ ^ 3 ≤ ε ^ 3 := by
      have h0 : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
      exact pow_le_pow_left₀ h0 hz 3
    have hz3nn : (0:ℝ) ≤ ‖z‖ ^ 3 := by positivity
    nlinarith [h1, hz3, hKge, hK, hz3nn]
  -- the two halves
  have hHy : ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ H :=
    le_trans (hH₀ y hyc) (le_max_left _ _)
  have hext := ext_avg_err_abs hφ hxy hε hK hTerr hHy hg (le_of_lt hgy)
  have havg : |⨍ z in ball (0 : EuclSpace d) ε, taylorErr φ y z|
      ≤ Ka * ε ^ 3 := by
    have h := hKa₀ y hyc ε hε hερ
    have hε3 : (0:ℝ) ≤ ε ^ 3 := by positivity
    have : Ka₀ * ε ^ 3 ≤ Ka * ε ^ 3 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) hε3
    linarith [h, this]
  exact expansion_err_le hd hp hpd hφ hε hext havg

end

end PLaplacian
