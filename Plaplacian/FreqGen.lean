/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.FreqProj

/-!
# The limit argument for a general filter

A correction to the two preceding files. The limit argument was stated for the
punctured neighbourhood of zero in the parameter, and the conditional assembly
accordingly asked for a frequency of a bound involving a function of the
parameter alone.

That is not what the chain supplies. The differential inequality holds at a
near-contact point, where the parameter and the point are coupled: the
quantity bounded depends on both, and the point is not determined by the
parameter, so no function of the parameter alone expresses it. The earlier
statements are true but their hypotheses cannot be discharged, which makes
them dead ends.

The repair is to state the argument for an arbitrary filter --- its proof
never needed otherwise --- and to run it on the product filter where the
contact points live. The earlier versions are this one specialised.

The error was in a statement rather than a proof, and it surfaced only on
attempting to connect the statement to what feeds it. That is the
characteristic failure of assembling a chain from both ends.

## Main results

- nonneg_of_frequently', nonpos_of_frequently'
- viscF_le_of_frequently_prod, le_viscF_of_frequently_prod
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The limit argument for a general filter

A correction. The earlier form of the limit argument was stated for the
punctured neighbourhood of zero in the parameter, and the conditional assembly
accordingly asked for a frequency of a bound involving a function of the
parameter alone.

That is not what the chain supplies. The differential inequality holds at a
near-contact point, where the parameter and the point are coupled: the
quantity bounded depends on both, and the point is not determined by the
parameter. So no function of the parameter alone expresses it.

The repair is to state the argument for an arbitrary filter, which its proof
never needed to avoid, and to run it on the product filter where the contact
points live. Nothing is lost: the earlier versions are the general one
specialised.
-/


/-- **The limit argument, for an arbitrary filter.** -/
theorem nonneg_of_frequently' {α : Type*} {F : Filter α} {I : ℝ}
    {q : α → ℝ} (hq : Filter.Tendsto q F (nhds 0))
    (hfreq : ∃ᶠ a in F, q a ≤ I) :
    0 ≤ I := by
  by_contra hcon
  push Not at hcon
  have hev : ∀ᶠ a in F, I < q a := hq.eventually (eventually_gt_nhds hcon)
  have hboth := hfreq.and_eventually hev
  rw [Filter.frequently_iff] at hboth
  obtain ⟨a, _, hle, hlt⟩ := hboth Filter.univ_mem
  linarith [hle, hlt]

/-- And the dual. -/
theorem nonpos_of_frequently' {α : Type*} {F : Filter α} {I : ℝ}
    {q : α → ℝ} (hq : Filter.Tendsto q F (nhds 0))
    (hfreq : ∃ᶠ a in F, I ≤ q a) :
    I ≤ 0 := by
  by_contra hcon
  push Not at hcon
  have hev : ∀ᶠ a in F, q a < I := hq.eventually (eventually_lt_nhds hcon)
  have hboth := hfreq.and_eventually hev
  rw [Filter.frequently_iff] at hboth
  obtain ⟨a, _, hge, hlt⟩ := hboth Filter.univ_mem
  linarith [hge, hlt]

/-- **The subsolution inequality, on the product filter.**

The form the chain can supply: the bound is frequent along the filter where
the contact points live, and the quantity may depend on both coordinates. -/
theorem viscF_le_of_frequently_prod {p : ℝ} {φ : EuclSpace d → ℝ}
    {x₀ : EuclSpace d} {Q : ℝ × EuclSpace d → ℝ}
    (hQ : Filter.Tendsto Q (relaxFilter x₀) (nhds 0))
    (hfreq : ∃ᶠ r in relaxFilter x₀,
      Q r ≤ normPLapOf p (gradient φ x₀) (fderiv ℝ (fderiv ℝ φ) x₀)) :
    viscF p (gradient φ x₀) (hess φ x₀) ≤ 0 :=
  viscF_le_of_chain (nonneg_of_frequently' hQ hfreq)

/-- The dual, on the product filter. -/
theorem le_viscF_of_frequently_prod {p : ℝ} {φ : EuclSpace d → ℝ}
    {x₀ : EuclSpace d} {Q : ℝ × EuclSpace d → ℝ}
    (hQ : Filter.Tendsto Q (relaxFilter x₀) (nhds 0))
    (hfreq : ∃ᶠ r in relaxFilter x₀,
      normPLapOf p (gradient φ x₀) (fderiv ℝ (fderiv ℝ φ) x₀) ≤ Q r) :
    0 ≤ viscF p (gradient φ x₀) (hess φ x₀) :=
  le_viscF_of_chain (nonpos_of_frequently' hQ hfreq)

end

end PLaplacian
