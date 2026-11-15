/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Singular

@[expose] public section

/-!
# Open and closed ball extreme values agree

The step operator takes its extreme values over open balls. That was forced by
measurability and is the first structural finding of this development: over
closed balls the supremum operator does not preserve Borel measurability, so
the admissible class is not invariant.

The extreme-value expansion, by contrast, was proved over closed balls, since
attainment of the supremum needs compactness.

For continuous functions the two agree, and this file proves it. The closed
ball is the closure of the open one, and a continuous image of a closure lies
in the closure of the image, whose supremum is the same because the set of
reals below a supremum is closed.

This is the one place in the development where the open-ball choice must be
paid for rather than merely respected. Everywhere else the two notions never
meet: the discrete theory uses open balls throughout, and the asymptotics use
closed ones throughout, and only the final composition needs them to be the
same.

## Main results

- sSup_ball_eq_closedBall
- sInf_ball_eq_closedBall
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## Open and closed balls

The step operator takes its extreme values over **open** balls, forced by
measurability and the first structural finding of this development. The
extreme-value expansion was proved over **closed** balls, since attainment
needs compactness.

For continuous functions the two agree, and this file proves it. It is the one
place in the development where the open-ball choice has to be paid for rather
than merely respected: everywhere else the two never meet.
-/

theorem sSup_ball_le_sSup_closedBall {φ : EuclSpace d → ℝ}
    (hφ : Continuous φ) (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    sSup (φ '' ball x ε) ≤ sSup (φ '' closedBall x ε) := by
  have hne : (φ '' ball x ε).Nonempty := ⟨φ x, ⟨x, mem_ball_self hε, rfl⟩⟩
  have hbdd : BddAbove (φ '' closedBall x ε) :=
    ((isCompact_closedBall x ε).image hφ).bddAbove
  refine csSup_le hne ?_
  rintro a ⟨y, hy, rfl⟩
  exact le_csSup hbdd ⟨y, ball_subset_closedBall hy, rfl⟩

theorem sSup_closedBall_le_sSup_ball {φ : EuclSpace d → ℝ}
    (hφ : Continuous φ) (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    sSup (φ '' closedBall x ε) ≤ sSup (φ '' ball x ε) := by
  have hcl : φ '' closedBall x ε ⊆ closure (φ '' ball x ε) := by
    rw [← closure_ball x hε.ne']
    exact image_closure_subset_closure_image hφ
  have hbdd : BddAbove (φ '' ball x ε) := by
    have h := ((isCompact_closedBall x ε).image hφ).bddAbove
    exact h.mono (Set.image_mono ball_subset_closedBall)
  have hne : (φ '' closedBall x ε).Nonempty :=
    ⟨φ x, ⟨x, mem_closedBall_self hε.le, rfl⟩⟩
  refine csSup_le hne ?_
  intro a ha
  have ha' : a ∈ closure (φ '' ball x ε) := hcl ha
  have hsub : closure (φ '' ball x ε) ⊆ Iic (sSup (φ '' ball x ε)) := by
    refine closure_minimal ?_ isClosed_Iic
    intro b hb
    exact le_csSup hbdd hb
  exact hsub ha'

/-- **The suprema agree.** -/
theorem sSup_ball_eq_closedBall {φ : EuclSpace d → ℝ} (hφ : Continuous φ)
    (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    sSup (φ '' ball x ε) = sSup (φ '' closedBall x ε) :=
  le_antisymm (sSup_ball_le_sSup_closedBall hφ x hε)
    (sSup_closedBall_le_sSup_ball hφ x hε)

/-- **And the infima**, by applying the above to the negation. -/
theorem sInf_ball_eq_closedBall {φ : EuclSpace d → ℝ} (hφ : Continuous φ)
    (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    sInf (φ '' ball x ε) = sInf (φ '' closedBall x ε) := by
  have hneg : Continuous (fun y => -φ y) := hφ.neg
  have h := sSup_ball_eq_closedBall hneg x hε
  have himg : ∀ s : Set (EuclSpace d),
      (fun y => -φ y) '' s = -(φ '' s) := by
    intro s
    ext a
    simp only [Set.mem_image, Set.mem_neg]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by ring⟩
    · rintro ⟨y, hy, hay⟩
      exact ⟨y, hy, by linarith [hay]⟩
  rw [himg, himg, Real.sSup_neg, Real.sSup_neg] at h
  linarith [h]


end

end PLaplacian
