/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.StrictComp

/-! # The foundations of the theorem of sums: statements

The theorem of sums is proved from two results of real analysis, Alexandrov's
theorem and Jensen's lemma, through sup-convolutions. This file fixes their
statements, in the language of the jets already defined, so that the proof of
the theorem of sums from them can be written and checked before either is
proved. The same discipline fixed the statement of the theorem of sums before
the comparison principle was proved from it.

## Twice differentiability in the sense of Peano

`f` is twice differentiable at `x` with gradient `q` and second derivative `X`
when `(q, X)` is both a superjet and a subjet there: `f` agrees with its
second-order polynomial up to `o(‖y - x‖²)`. This is weaker than twice
Fréchet differentiability, and is exactly what Alexandrov's theorem provides.

## Alexandrov's theorem

A convex function on the whole space is twice differentiable in the sense of
Peano at almost every point. The proof we intend goes through the proximal map
`(I + ∂f)⁻¹`, which is single-valued and one-Lipschitz, Rademacher's theorem
for it, and the area formula for the points where its derivative is singular;
Rademacher's theorem and the area formula are in Mathlib.

## Jensen's lemma

If a semiconvex function has a strict maximum at a point on a closed ball,
then for every `δ > 0` the set of points of the open ball at which some
perturbation `w + ⟪p, ·⟫` with `‖p‖ ≤ δ` has a local maximum has positive
measure. [CIL92, Lemma A.3]. Semiconvexity is stated as convexity of
`w + (λ/2) ‖·‖²`.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- **Twice differentiability in the sense of Peano.** -/
def TwiceDiffAt (f : EuclSpace d → ℝ) (x q : EuclSpace d) (X : Bilin d) : Prop :=
  (q, X) ∈ SuperJet f x ∧ (q, X) ∈ SubJet f x

/-- **Semiconvexity**, with constant `lam`. -/
def SemiconvexWith (lam : ℝ) (w : EuclSpace d → ℝ) : Prop :=
  ConvexOn ℝ univ (fun x => w x + (lam / 2) * ‖x‖ ^ 2)

/-- **Alexandrov's theorem**, stated as a proposition. -/
def AlexandrovThm (d : ℕ) : Prop :=
  ∀ f : EuclSpace d → ℝ, ConvexOn ℝ univ f →
    ∀ᵐ x ∂(volume : Measure (EuclSpace d)), ∃ q X, TwiceDiffAt f x q X

/-- **Jensen's lemma**, stated as a proposition. -/
def JensenLemma (d : ℕ) : Prop :=
  ∀ (w : EuclSpace d → ℝ) (lam : ℝ), SemiconvexWith lam w →
    ∀ (xh : EuclSpace d) (r : ℝ), 0 < r →
      (∀ y ∈ closedBall xh r, y ≠ xh → w y < w xh) →
      ∀ δ > 0, 0 < (volume : Measure (EuclSpace d))
        {x ∈ ball xh r | ∃ p : EuclSpace d, ‖p‖ ≤ δ ∧
          IsLocalMax (fun y => w y + inner ℝ p y) x}

/-- Peano twice differentiability gives a superjet. -/
theorem TwiceDiffAt.superJet {f : EuclSpace d → ℝ} {x q : EuclSpace d}
    {X : Bilin d} (h : TwiceDiffAt f x q X) : (q, X) ∈ SuperJet f x := h.1

/-- And a subjet. -/
theorem TwiceDiffAt.subJet {f : EuclSpace d → ℝ} {x q : EuclSpace d}
    {X : Bilin d} (h : TwiceDiffAt f x q X) : (q, X) ∈ SubJet f x := h.2

/-- A set of positive measure meets every set of full measure. -/
theorem exists_mem_of_pos_of_ae {s : Set (EuclSpace d)}
    (hs : 0 < (volume : Measure (EuclSpace d)) s) {P : EuclSpace d → Prop}
    (hP : ∀ᵐ x ∂(volume : Measure (EuclSpace d)), P x) :
    ∃ x ∈ s, P x := by
  by_contra h
  push Not at h
  have hsub : s ⊆ {x | ¬ P x} := fun x hx => h x hx
  have h0 : (volume : Measure (EuclSpace d)) {x | ¬ P x} = 0 :=
    ae_iff.1 hP
  have := measure_mono_null hsub h0
  rw [this] at hs
  exact lt_irrefl 0 hs

end

end PLaplacian
