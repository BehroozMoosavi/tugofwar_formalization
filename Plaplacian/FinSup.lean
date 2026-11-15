/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.AddSmooth

@[expose] public section

/-!
# Finite families of subsolutions

The maximum over a nonempty finite family of subsolutions is a subsolution, by
induction from the binary case of `Plaplacian.MaxSub`. No envelope is needed,
because a finite maximum of upper semicontinuous functions is upper
semicontinuous.

## The infinite case

For an infinite family the supremum need not be upper semicontinuous, so one
must pass to the upper semicontinuous envelope, and then a contact point for
the envelope is not a contact point for any single member of the family. The
standard proof constructs sequences of points and indices along which the
family approaches the envelope, perturbs the test function to create genuine
contact points, and passes to the limit using continuity of the first and
second derivatives of the test function.

That argument is essentially the half-relaxed limit stability theorem, and it
is the natural first piece of the convergence layer rather than an addendum
here. It is also where the reals failing to be a complete lattice finally
matters: the envelope requires a uniform bound, since the supremum of an
unbounded family is a junk value, and must be built from the open-preimage
characterisation of semicontinuity rather than from `liminf`.

## Main results

- `IsViscositySubsolution.finsetSup'`
-/

open Set Topology Filter

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ## Finite families

The maximum over a nonempty finite family of subsolutions is a subsolution, by
induction from the binary case. No envelope is needed: a finite maximum of
upper semicontinuous functions is upper semicontinuous.

The infinite case is a different theorem; see the note at the end of the file.
-/


/-- The maximum over a nonempty finite family of subsolutions. -/
theorem IsViscositySubsolution.finsetSup' {p : ℝ} {Ω : Set (EuclSpace d)}
    {f : EuclSpace d → ℝ} {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (u : ι → EuclSpace d → ℝ)
    (hu : ∀ i ∈ s, IsViscositySubsolution p Ω f (u i)) :
    IsViscositySubsolution p Ω f (fun y => s.sup' hs (fun i => u i y)) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
      have h := hu i (by simp)
      have heq : (fun y => ({i} : Finset ι).sup'
          (Finset.singleton_nonempty i) (fun j => u j y)) = u i := by
        funext y
        simp
      rw [heq]
      exact h
  | cons i t hit ht ih =>
      have hui : IsViscositySubsolution p Ω f (u i) := hu i (by simp)
      have hut : ∀ j ∈ t, IsViscositySubsolution p Ω f (u j) := by
        intro j hj
        exact hu j (by simp [hj])
      have hih := ih hut
      simp only [Finset.sup'_cons ht]
      exact IsViscositySubsolution.max hui hih

end

end PLaplacian
