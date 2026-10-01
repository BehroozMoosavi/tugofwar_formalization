/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Transfer

/-!
# The near-maximizer at a coupled tolerance

The repair of the gap in the convergence route.

The near-contact slack must shrink with the parameter, and the near-contact as
first set up could not supply that, because its tolerance was measured against
the limit of the difference --- a limiting quantity, which cannot be tied to
the parameter, the limit superior giving approach without a rate.

The right measure is the parameter's own supremum over the closed ball, which
is finite. A near-maximizer at any tolerance then exists by the definition of
supremum alone. Taking the tolerance to be the cube of the parameter, the
comparison applies with the supremum as its constant and the cube as its
slack, and the slack divided by the squared parameter is the parameter itself,
which tends to zero.

The comparison never needed the difference near the limit. It needs only the
bound by the supremum on the ball, true by definition, and the near-equality
at the chosen point, true by choice. What we had taken for a structural gap
was a choice of reference point.

What remains is that the near-maximizers converge to the base point, which
uses the strictness of the local maximum and is the standard compactness step.
It has no rate problem.

## Main results

- exists_near_sup
- exists_near_sup_cube
- le_sup_on_ball
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The near-maximizer at a coupled tolerance: the fix

The gap in the route was that the near-contact slack must shrink with the
parameter, and the near-contact as first set up could not supply that.

The error was in the set-up, not the mathematics. The tolerance was measured
against the limit `M = ubar u x₀ - φ x₀`, a limiting quantity, so it could not
be tied to the parameter. The right measure is the parameter's own supremum

  `S ε = sup over the closed ball of (u ε - φ)`,

which is finite. A near-maximizer at any tolerance --- in particular at `ε³`
--- then exists by the definition of supremum alone, with no rate required of
the limit superior. The comparison applies with `c = S ε` and slack `ε³`, and
`ε³ / ε² = ε` tends to zero.

So the comparison never needed the difference near the limit. It needs only
the bound by `S ε` on the ball, true by definition, and the near-equality at
the chosen point, true by choice.
-/


/-- **A near-maximizer at any tolerance.** For a function bounded above on a
nonempty set, some point of the set has value within any tolerance of the
supremum. -/
theorem exists_near_sup {s : Set (EuclSpace d)} (hs : s.Nonempty)
    {f : EuclSpace d → ℝ} (_hbdd : BddAbove (f '' s)) {τ : ℝ} (hτ : 0 < τ) :
    ∃ y ∈ s, sSup (f '' s) - τ < f y := by
  have hne : (f '' s).Nonempty := hs.image f
  have hlt : sSup (f '' s) - τ < sSup (f '' s) := by linarith
  obtain ⟨_, ⟨y, hy, rfl⟩, hval⟩ := exists_lt_of_lt_csSup hne hlt
  exact ⟨y, hy, hval⟩

/-- **The near-maximizer at tolerance `ε³`**, for the family on a closed ball.

The tolerance depends on the parameter, which is exactly what the earlier
set-up could not provide. -/
theorem exists_near_sup_cube (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {φ : EuclSpace d → ℝ} {B : ℝ}
    (hB : ∀ y, |φ y| ≤ B) (x₀ : EuclSpace d) {r : ℝ} (hr : 0 < r)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ closedBall x₀ r,
      sSup ((fun w => u ε w - φ w) '' closedBall x₀ r) - ε ^ 3
        < u ε y - φ y := by
  have hs : (closedBall x₀ r).Nonempty := ⟨x₀, mem_closedBall_self hr.le⟩
  have hbdd : BddAbove ((fun w => u ε w - φ w) '' closedBall x₀ r) := by
    refine ⟨C + B, ?_⟩
    rintro a ⟨w, _, rfl⟩
    have h1 := abs_le.1 (hC ε w)
    have h2 := abs_le.1 (hB w)
    linarith [h1.2, h2.1]
  have hτ : (0:ℝ) < ε ^ 3 := by positivity
  exact exists_near_sup hs hbdd hτ

/-- The family minus the test function is bounded by its supremum on the
ball, which is the comparison's first hypothesis. -/
theorem le_sup_on_ball (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {φ : EuclSpace d → ℝ} {B : ℝ}
    (hB : ∀ y, |φ y| ≤ B) (x₀ : EuclSpace d) {r ε : ℝ} :
    ∀ w ∈ closedBall x₀ r,
      u ε w - φ w ≤ sSup ((fun w => u ε w - φ w) '' closedBall x₀ r) := by
  intro w hw
  have hbdd : BddAbove ((fun w => u ε w - φ w) '' closedBall x₀ r) := by
    refine ⟨C + B, ?_⟩
    rintro a ⟨v, _, rfl⟩
    have h1 := abs_le.1 (hC ε v)
    have h2 := abs_le.1 (hB v)
    linarith [h1.2, h2.1]
  exact le_csSup hbdd ⟨w, hw, rfl⟩

end

end PLaplacian
