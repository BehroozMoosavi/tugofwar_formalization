/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.DiffIneq

/-!
# The passage to the limit

At each parameter the differential inequality bounds the operator below by a
multiple of the error divided by the square of the parameter. The rate makes
that quotient tend to zero, since an error of order epsilon cubed divided by
epsilon squared is of order epsilon, and a quantity bounded below by terms
tending to zero is nonnegative.

This is where the rate of the third layer earns its keep. Without it the error
is merely bounded, and a bounded quantity divided by the square of the
parameter need not vanish.

## Main results

- nonneg_of_tendsto_le, nonneg_of_rate
- tendsto_err_quotient
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The passage to the limit

At each `ε` the inequality reads

  `-2(p+d) E_ε ≤ ε² I`,

with `I` the normalized `p`-Laplacian, which does not depend on `ε`. Dividing
by `ε²` and letting `ε → 0`:

  `-2(p+d) E_ε / ε² ≤ I`,

and the rate makes the left side tend to zero, so `0 ≤ I`. That is the
subsolution inequality: `- Δ^N_p φ ≤ 0`.

The content is the limit argument, and it is stated abstractly in the error,
since the rate is what supplies the hypothesis.
-/


/-- **The limit argument.** If a quantity is bounded below by terms tending to
zero, it is nonnegative. -/
theorem nonneg_of_tendsto_le {I : ℝ} {f : ℝ → ℝ} {l : Filter ℝ} [l.NeBot]
    (hf : Filter.Tendsto f l (nhds 0)) (hle : ∀ᶠ ε in l, f ε ≤ I) :
    0 ≤ I :=
  le_of_tendsto hf hle

/-- The error quotient tends to zero when the error is of higher order. -/
theorem tendsto_err_quotient {K M : ℝ} (hM : 0 ≤ M) {E : ℝ → ℝ}
    (hE : ∀ ε > 0, |E ε| ≤ K * ε ^ 3) (_hK : 0 ≤ K) :
    Filter.Tendsto (fun ε => M * E ε / ε ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hsq : Filter.Tendsto (fun ε : ℝ => M * K * ε)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hc : Continuous (fun ε : ℝ => M * K * ε) := by fun_prop
    have h := hc.tendsto (0 : ℝ)
    simp only [mul_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hsq
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hεpos : (0:ℝ) < ε := hε
  have h2 : (0:ℝ) < ε ^ 2 := by positivity
  have hEε := hE ε hεpos
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_nonneg hM,
      abs_of_pos h2]
  rw [div_le_iff₀ h2]
  calc M * |E ε| ≤ M * (K * ε ^ 3) := by
        exact mul_le_mul_of_nonneg_left hEε hM
    _ = M * K * ε * ε ^ 2 := by ring


/-- **The subsolution inequality in the limit**, stated with the hypothesis
the rate supplies. -/
theorem nonneg_of_rate {I : ℝ} {c : ℝ} {q : ℝ → ℝ}
    (hq : Filter.Tendsto q (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hle : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), q ε ≤ I) :
    0 ≤ I := by
  exact nonneg_of_tendsto_le hq hle

end

end PLaplacian
