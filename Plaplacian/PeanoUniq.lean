/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.CompFull

@[expose] public section

/-! # Peano expansions: the `C²` case, and uniqueness

1. A `C²` function has the Peano expansion `(∇φ, D²φ)` at every point: this is
   the Taylor bound `exists_taylorErr_le`, with `⟪∇φ(x), w⟫ = Dφ(x) w`.
2. Two expansions of one function at one point have the same gradient and the
   same quadratic form: their difference expands the zero function, which has a
   maximum everywhere, and `max_peano` applies both ways round.
3. `Δᴺₚ` sees only the quadratic form.
4. Hence for a `C²` function with any expansion `(q, X)`,
   `Δᴺₚ(∇φ, D²φ) = Δᴺₚ(q, X)`: the operator value can be read off an explicit
   expansion, without computing a Hessian.
-/

open Set Topology Filter Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- **A `C²` function has the expansion `(∇φ, D²φ)`.** -/
theorem peanoAt_of_contDiff {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ) (x : EuclSpace d) :
    PeanoAt φ x (gradient φ x) (hess φ x) := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := exists_taylorErr_le hφ x hε
  refine ⟨δ, hδ, fun k hk => ?_⟩
  have h := hb k hk
  unfold taylorErr at h
  have hg : inner ℝ (gradient φ x) k = fderiv ℝ φ x k := by
    unfold gradient
    exact InnerProductSpace.toDual_symm_apply
  rw [hg]
  unfold hess
  exact h

/-- **Peano expansions are unique.** -/
theorem peano_unique {f : EuclSpace d → ℝ} {x q q' : EuclSpace d} {X X' : Bilin d}
    (h1 : PeanoAt f x q X) (h2 : PeanoAt f x q' X') :
    q = q' ∧ ∀ v, (X v) v = (X' v) v := by
  have hz : ∀ᶠ z in 𝓝 x, (fun y => f y - f y) z ≤ (fun y => f y - f y) x :=
    Eventually.of_forall fun z => by simp
  obtain ⟨hq, hX⟩ := max_peano (peanoAt_sub h1 h2) hz
  obtain ⟨_, hX'⟩ := max_peano (peanoAt_sub h2 h1) hz
  refine ⟨sub_eq_zero.1 hq, fun v => ?_⟩
  have a := hX v
  have b := hX' v
  rw [sub_apply, sub_apply] at a b
  linarith

/-- **The operator sees only the quadratic form.** -/
theorem normPLapOf_congr {p : ℝ} {X X' : Bilin d} (h : ∀ v, (X v) v = (X' v) v)
    (q : EuclSpace d) : normPLapOf p q X = normPLapOf p q X' := by
  unfold normPLapOf infLaplacianOf laplacianOf
  simp only [h]

/-- **The operator value of a `C²` function, from any expansion.** -/
theorem normPLapOf_of_peano {p : ℝ} {φ : EuclSpace d → ℝ} (hφ : ContDiff ℝ 2 φ)
    {x q : EuclSpace d} {X : Bilin d} (hP : PeanoAt φ x q X) :
    gradient φ x = q ∧ normPLapOf p (gradient φ x) (hess φ x) = normPLapOf p q X := by
  obtain ⟨hq, hX⟩ := peano_unique (peanoAt_of_contDiff hφ x) hP
  refine ⟨hq, ?_⟩
  rw [hq]
  exact normPLapOf_congr hX q

end

end PLaplacian
