/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Stability

@[expose] public section

/-!
# The maximum of two subsolutions

The classical statement is that the supremum of a family of subsolutions is a
subsolution, after passing to the upper semicontinuous envelope. We prove the
binary case, where no envelope is needed: the maximum of two upper
semicontinuous functions is upper semicontinuous, whereas the supremum of an
infinite family need not be.

The argument is a case split on which function attains the maximum at the
contact point. If `max u v - φ` has a local maximum at `x0` and `u x0` attains
the max there, then `u - φ` has a local maximum at `x0` as well, because

  `u y - φ y <= max (u y) (v y) - φ y <= max (u x0) (v x0) - φ x0
              = u x0 - φ x0`,

so the subsolution property of `u` applies and gives the required inequality.
The gradient and Hessian of the test function are the same in either branch, so
no further work is needed.

## On the infinite case

The general family needs the upper semicontinuous envelope, and there the
reals failing to be a complete lattice does bite: `sSup` of an unbounded family
is a junk value, so a uniform bound is required, and the envelope must be built
from the open-preimage characterisation of semicontinuity rather than from
`liminf`. That is left as future work, and is arguably not needed for the
convergence proof, which uses the envelope of a *limit* rather than the
supremum of a family.

## Main results

- `IsViscositySubsolution.max`
-/

open Set Topology Filter

noncomputable section

variable {d : ℕ}

namespace PLaplacian

/-- At a contact point for the maximum, the test function also touches whichever
function attains the maximum there. -/
theorem isLocalMax_of_attains_left {u v φ : EuclSpace d → ℝ}
    {x₀ : EuclSpace d}
    (hmax : IsLocalMax (fun y => max (u y) (v y) - φ y) x₀)
    (hattain : u x₀ = max (u x₀) (v x₀)) :
    IsLocalMax (fun y => u y - φ y) x₀ := by
  filter_upwards [hmax] with y hy
  have h1 : u y ≤ max (u y) (v y) := le_max_left _ _
  rw [hattain]
  linarith

/-- The same on the right. -/
theorem isLocalMax_of_attains_right {u v φ : EuclSpace d → ℝ}
    {x₀ : EuclSpace d}
    (hmax : IsLocalMax (fun y => max (u y) (v y) - φ y) x₀)
    (hattain : v x₀ = max (u x₀) (v x₀)) :
    IsLocalMax (fun y => v y - φ y) x₀ := by
  filter_upwards [hmax] with y hy
  have h1 : v y ≤ max (u y) (v y) := le_max_right _ _
  rw [hattain]
  linarith

/-- **The maximum of two subsolutions is a subsolution.** -/
theorem IsViscositySubsolution.max {p : ℝ} {Ω : Set (EuclSpace d)}
    {f u v : EuclSpace d → ℝ}
    (hu : IsViscositySubsolution p Ω f u)
    (hv : IsViscositySubsolution p Ω f v) :
    IsViscositySubsolution p Ω f (fun y => max (u y) (v y)) where
  usc := UpperSemicontinuousOn.sup hu.usc hv.usc
  regular := fun φ hφ x₀ hx₀ hmax hgrad => by
    rcases max_cases (u x₀) (v x₀) with ⟨heq, -⟩ | ⟨heq, -⟩
    · exact hu.regular φ hφ x₀ hx₀
        (isLocalMax_of_attains_left hmax heq.symm) hgrad
    · exact hv.regular φ hφ x₀ hx₀
        (isLocalMax_of_attains_right hmax heq.symm) hgrad
  singular := fun φ hφ x₀ hx₀ hmax hgrad => by
    rcases max_cases (u x₀) (v x₀) with ⟨heq, -⟩ | ⟨heq, -⟩
    · exact hu.singular φ hφ x₀ hx₀
        (isLocalMax_of_attains_left hmax heq.symm) hgrad
    · exact hv.singular φ hφ x₀ hx₀
        (isLocalMax_of_attains_right hmax heq.symm) hgrad

/-- Dually, the minimum of two supersolutions is a supersolution. -/
theorem isLocalMin_of_attains_left {u v φ : EuclSpace d → ℝ}
    {x₀ : EuclSpace d}
    (hmin : IsLocalMin (fun y => min (u y) (v y) - φ y) x₀)
    (hattain : u x₀ = min (u x₀) (v x₀)) :
    IsLocalMin (fun y => u y - φ y) x₀ := by
  filter_upwards [hmin] with y hy
  have h1 : min (u y) (v y) ≤ u y := min_le_left _ _
  rw [hattain]
  linarith

theorem isLocalMin_of_attains_right {u v φ : EuclSpace d → ℝ}
    {x₀ : EuclSpace d}
    (hmin : IsLocalMin (fun y => min (u y) (v y) - φ y) x₀)
    (hattain : v x₀ = min (u x₀) (v x₀)) :
    IsLocalMin (fun y => v y - φ y) x₀ := by
  filter_upwards [hmin] with y hy
  have h1 : min (u y) (v y) ≤ v y := min_le_right _ _
  rw [hattain]
  linarith

theorem IsViscositySupersolution.min {p : ℝ} {Ω : Set (EuclSpace d)}
    {f u v : EuclSpace d → ℝ}
    (hu : IsViscositySupersolution p Ω f u)
    (hv : IsViscositySupersolution p Ω f v) :
    IsViscositySupersolution p Ω f (fun y => min (u y) (v y)) where
  lsc := LowerSemicontinuousOn.inf hu.lsc hv.lsc
  regular := fun φ hφ x₀ hx₀ hmin hgrad => by
    rcases min_cases (u x₀) (v x₀) with ⟨heq, -⟩ | ⟨heq, -⟩
    · exact hu.regular φ hφ x₀ hx₀
        (isLocalMin_of_attains_left hmin heq.symm) hgrad
    · exact hv.regular φ hφ x₀ hx₀
        (isLocalMin_of_attains_right hmin heq.symm) hgrad
  singular := fun φ hφ x₀ hx₀ hmin hgrad => by
    rcases min_cases (u x₀) (v x₀) with ⟨heq, -⟩ | ⟨heq, -⟩
    · exact hu.singular φ hφ x₀ hx₀
        (isLocalMin_of_attains_left hmin heq.symm) hgrad
    · exact hv.singular φ hφ x₀ hx₀
        (isLocalMin_of_attains_right hmin heq.symm) hgrad

end PLaplacian

end
