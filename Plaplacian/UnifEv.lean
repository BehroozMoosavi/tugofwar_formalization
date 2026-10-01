/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.Annulus

/-!
# The uniform eventual bound on the annulus

The gap on the annulus is a pointwise statement about the relaxed limit. Here
it becomes a bound on the family itself, uniform over the annulus and eventual
in the parameter.

At each point of the annulus there is a parameter set and a neighbourhood on
which the family minus the test function is below the target. The
neighbourhoods cover the annulus, compactness gives finitely many, and the
intersection of their parameter sets is a filter member.

The library has a lemma packaging this argument, but it works with the
two-sided neighbourhood of a pair, while the relaxed filter is one-sided in
the parameter, so the hypothesis it needs is stronger than the one available.
The finite subcover is therefore done by hand, which has the incidental
advantage that the quantifier order --- the parameter set chosen before both
the parameter and the point --- is visible in the proof.

## Main results

- pointwise_bound
- uniform_bound_annulus
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The uniform eventual bound

The library lemma `IsCompact.eventually_forall_of_forall_eventually` works with
the two-sided neighbourhood of a pair, whereas the relaxed filter is one-sided
in the parameter: the hypothesis available covers positive parameters only. So
the lemma does not apply directly, and the finite subcover is done by hand.

At each point of the annulus there is a parameter set and a neighbourhood on
which the family minus the test function is below the target. The
neighbourhoods cover the annulus, compactness gives finitely many, and the
intersection of their parameter sets is a filter member.
-/

/-- Pointwise: at each point of the annulus, a parameter set and a
neighbourhood carrying the bound. -/
theorem pointwise_bound (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {φ : EuclSpace d → ℝ}
    (hφ : Continuous φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B)
    {x₀ : EuclSpace d} {ρ r a : ℝ}
    (hgap : ∀ w ∈ annulus x₀ ρ r, ubar u w - φ w < a) :
    ∀ w ∈ annulus x₀ ρ r,
      ∃ S ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0), ∃ V ∈ nhds w,
        ∀ ε ∈ S, ∀ y ∈ V, u ε y - φ y < a := by
  intro w hw
  have hbd := abs_sub_le_of_bounds u hC hB
  have heq := ubar_sub u hC hφ hB w
  have hlt : ubar (fun ε y => u ε y - φ y) w < a := by
    rw [heq]; exact hgap w hw
  exact exists_prod_nhds_of_ubar_lt (fun ε y => u ε y - φ y) hbd w hlt

/-- **The uniform eventual bound on the annulus.** -/
theorem uniform_bound_annulus (u : ℝ → EuclSpace d → ℝ) {C : ℝ}
    (hC : ∀ ε y, |u ε y| ≤ C) {φ : EuclSpace d → ℝ}
    (hφ : Continuous φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B)
    {x₀ : EuclSpace d} {ρ r a : ℝ}
    (hgap : ∀ w ∈ annulus x₀ ρ r, ubar u w - φ w < a) :
    ∃ S ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ ε ∈ S, ∀ y ∈ annulus x₀ ρ r, u ε y - φ y < a := by
  have hpt := pointwise_bound u hC hφ hB hgap
  -- choose the parameter set and neighbourhood at each point
  choose! Sf hSf Vf hVf hbd using hpt
  -- a finite subcover of the annulus by the neighbourhoods
  obtain ⟨t, ht, hcover⟩ :=
    (isCompact_annulus x₀ ρ r).elim_nhds_subcover Vf hVf
  -- the intersection of the finitely many parameter sets
  refine ⟨⋂ w ∈ t, Sf w, ?_, ?_⟩
  · exact (Filter.biInter_finset_mem t).2 (fun w hw => hSf w (ht w hw))
  · intro ε hε y hy
    obtain ⟨w, hwt, hyw⟩ := Set.mem_iUnion₂.1 (hcover hy)
    have hεw : ε ∈ Sf w := Set.mem_iInter₂.1 hε w hwt
    exact hbd w (ht w hwt) ε hεw y hyw

end

end PLaplacian
