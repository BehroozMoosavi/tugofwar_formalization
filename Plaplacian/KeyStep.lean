/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Relaxed

@[expose] public section

/-!
# The key convergence step

If the difference of a solution and a test function attains its maximum at an
interior point, then the test function satisfies the discrete inequality
there.

This is the theorem the first three layers were built for, and it consumes
three of the first layer in one argument: monotonicity pushes the pointwise
inequality through the operator, translation equivariance pulls the constant
out, and the dynamic programming principle replaces the operator applied to
the solution by the solution itself.

Combined with the expansion of the third layer, the conclusion becomes a
statement about the normalized p-Laplacian at order epsilon squared, and the
rate makes the error vanish in the limit. What remains for convergence is the
extraction of a sequence of contact points, which is the same theorem as the
stability of an infinite family of subsolutions, deferred from the viscosity
layer for that reason.

## Main results

- dpp_comparison
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The key convergence step

If `u ε - φ` has a local maximum at `y`, then comparing the two at `y` and
applying the operator gives the differential inequality in the limit. The
chain is:

* `u ε - φ ≤ c` near `y` with equality at `y`, where `c = u ε y - φ y`;
* monotonicity and translation equivariance give
  `T_ε (u ε) y ≤ T_ε φ y + c`;
* the dynamic programming principle says `u ε y = T_ε (u ε) y`, so
  `φ y ≤ T_ε φ y`;
* the expansion turns that into
  `0 ≤ ε²/(2(p+d)) Δ^N_p φ y + E`;
* dividing by `ε²` and letting `ε → 0`, the rate makes `E/ε²` vanish, so
  `0 ≤ Δ^N_p φ`, which is the subsolution inequality.

This file proves the steps up to the differential inequality at fixed `ε`.
The passage to the limit needs the sequence extraction, which is deferred.
-/


/-- **Comparison through the operator.** If `u - φ` is bounded by `c`
everywhere and `u` is `p`-harmonious at an interior point, then `φ` is a
subsolution of the discrete equation there. -/
theorem dpp_comparison {p ε : ℝ} (hp : 2 ≤ p) (hd : 0 < d) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} {F u φ : EuclSpace d → ℝ}
    (hu : IsPHarmonious p ε Ω F u) (hφ : BddMeas φ)
    {y : EuclSpace d} (hy : y ∈ Ω) {c : ℝ}
    (hle : ∀ w, u w - φ w ≤ c) (heq : u y - φ y = c) :
    φ y ≤ tugOfWarOp p ε φ y := by
  -- u ≤ φ + c pointwise
  have hup : ∀ w, u w ≤ φ w + c := by
    intro w
    linarith [hle w]
  -- monotonicity through the operator
  have hmono : tugOfWarOp p ε u y
      ≤ tugOfWarOp p ε (fun w => φ w + c) y := by
    refine tugOfWarOp_monotone p ε hp hd hε hu.bddMeas ?_ hup y
    exact ⟨hφ.meas.add measurable_const, by
      obtain ⟨B, hB⟩ := hφ.bound
      exact ⟨B + |c|, fun w => by
        have := hB w
        have := abs_le.1 this
        rw [abs_le]
        constructor <;> [linarith [abs_nonneg c, neg_abs_le c];
          linarith [le_abs_self c]]⟩⟩
  -- the constant comes out
  rw [tugOfWarOp_add_const p ε hε hφ c y hpd] at hmono
  -- the dynamic programming principle
  rw [← hu.interior y hy] at hmono
  -- and u y = φ y + c
  have huy : u y = φ y + c := by linarith [heq]
  rw [huy] at hmono
  linarith [hmono]

end

end PLaplacian
