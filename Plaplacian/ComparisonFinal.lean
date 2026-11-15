/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Plaplacian.UnifContinuity

@[expose] public section

/-!
# The comparison principle for the epsilon-Dirichlet problem

The components of Theorem 2.2 of Luiro-Parviainen-Saksman, proved in
`Plaplacian.Comparison`, assembled for solutions of the epsilon-Dirichlet
problem. At a point where the difference of two solutions attains its maximum,
both equal their operator values, so the difference is preserved by the
operator; that supplies the fixed-point hypothesis of
`not_bounded_max_set`, and boundedness of the domain gives the contradiction.

The hypothesis that the maximum is attained only inside the domain is stated
rather than derived. In the intended application it holds because the data
satisfies `v <= u` on the boundary strip, so a positive maximum cannot occur
there; but the epsilon-Dirichlet problem constrains nothing outside the
epsilon-closure, so it cannot be deduced without a further assumption on
behaviour at infinity.

## Main results

- `comparison_of_attained`, `not_attained_pos`
-/

open MeasureTheory Metric Set Filter

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-- **The comparison principle for solutions of the epsilon-Dirichlet
problem.**

If two `p`-harmonious functions have their difference attaining a positive
maximum, and that maximum is attained only inside the domain, the maximum set
is unbounded --- contradicting boundedness of the domain. Hence no positive
maximum is attained inside.

The hypothesis `hmaxΩ` is what the intended application supplies: on the
boundary strip the data satisfies `v ≤ u`, so a positive maximum of `v - u`
cannot be attained there. Isolating it keeps this theorem free of assumptions
about the behaviour of `u` and `v` outside `Ω_ε`, where the
`ε`-Dirichlet problem says nothing. -/
theorem comparison_of_attained (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} (hΩbdd : Bornology.IsBounded Ω)
    (e : EuclSpace d) (he : ‖e‖ = 1)
    {F G : EuclSpace d → ℝ} {u v : EuclSpace d → ℝ}
    (hu : IsPHarmonious p ε Ω F u) (hv : IsPHarmonious p ε Ω G v)
    {M : ℝ} (hMle : ∀ y, v y - u y ≤ M)
    (hmaxΩ : ∀ y, v y - u y = M → y ∈ Ω)
    {x₀ : EuclSpace d} (hx₀ : v x₀ - u x₀ = M) :
    False := by
  -- at a point of the maximum set the dynamic programming principle holds
  have hfix : ∀ y, v y - u y = M →
      tugOfWarOp p ε v y - tugOfWarOp p ε u y = v y - u y := by
    intro y hy
    have hyΩ : y ∈ Ω := hmaxΩ y hy
    have hue : u y = tugOfWarOp p ε u y := hu.interior y hyΩ
    have hve : v y = tugOfWarOp p ε v y := hv.interior y hyΩ
    rw [← hue, ← hve]
  exact not_bounded_max_set p ε hp hε hpd e he hu.bddMeas hv.bddMeas
    hMle hfix hx₀ hΩbdd (fun y hy => hmaxΩ y hy)

/-- **No positive maximum.** Under the same hypotheses, the difference cannot
attain a positive value that is its maximum. -/
theorem not_attained_pos (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ))
    {Ω : Set (EuclSpace d)} (hΩbdd : Bornology.IsBounded Ω)
    (e : EuclSpace d) (he : ‖e‖ = 1)
    {F G : EuclSpace d → ℝ} {u v : EuclSpace d → ℝ}
    (hu : IsPHarmonious p ε Ω F u) (hv : IsPHarmonious p ε Ω G v)
    {M : ℝ} (hMle : ∀ y, v y - u y ≤ M)
    (hmaxΩ : ∀ y, v y - u y = M → y ∈ Ω) :
    ¬ ∃ x₀, v x₀ - u x₀ = M := by
  rintro ⟨x₀, hx₀⟩
  exact comparison_of_attained p ε hp hε hpd hΩbdd e he hu hv hMle hmaxΩ hx₀

end

end PLaplacian
