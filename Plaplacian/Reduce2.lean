/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Reduce1

@[expose] public section

/-! # The reduction, part two: the convolutions inherit the strict maximum

Let `ũ` and `ṽ` vanish at zero, with `ũ` and `-ṽ` upper semicontinuous and
bounded above, and let `Ψ(ξ, ζ) = ũ(ξ) - ṽ(ζ) - P₀(ξ - ζ)` be negative off the
origin, `P₀ = ½ S + ‖·‖²`. With

  `λ = 8 M₀ + 1`,  `û = supConv λ ũ`,  `ň = supConv λ (-ṽ)`,  `v̌ = -ň`,

the convolved doubled function `û(ξ) - v̌(ζ) - 2P₀(ξ - ζ)` has a strict global
maximum, equal to zero, at the origin; and `û` and `-v̌ = ň` are semiconvex.
That is what `core_sequences` consumes.

* **Decoupling.** Young's inequality with `ε = 1` and
  `‖a - b‖² ≤ 2(‖a‖² + ‖b‖²)` give
  `P₀(x - y) ≤ 2P₀(ξ - ζ) + (λ/2)(‖x - ξ‖² + ‖y - ζ‖²)`.
* **The bound**: `û(ξ) + ň(ζ) ≤ 2P₀(ξ - ζ)`, both suprema bounded in turn.
* **At the origin** both convolutions are nonnegative with nonpositive sum, so
  both vanish.
* **Strictness**, by attainment: if both maximizers vanish, the term
  `-(λ/2)(‖ξ‖² + ‖ζ‖²)` is negative off the origin; otherwise `Ψ < 0` at the
  maximizers, and decoupling carries it through.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- The convolution parameter. -/
def lamC (α : ℝ) (h0 : EuclSpace d) : ℝ := 8 * penM (1 / 2) 1 α h0 + 1

theorem lamC_pos {α : ℝ} (hα : 0 < α) (h0 : EuclSpace d) : 0 < lamC α h0 := by
  unfold lamC
  have := penM_nonneg (h0 := h0) (by norm_num : (0:ℝ) ≤ 1 / 2) zero_le_one hα
  linarith

/-- `‖a - b‖² ≤ 2(‖a‖² + ‖b‖²)`. -/
theorem norm_sub_sq_le_two (a b : EuclSpace d) :
    ‖a - b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  rw [norm_sub_sq_real]
  have := young_inner (one_pos) a (-b)
  rw [inner_neg_right, norm_neg] at this
  linarith

/-- **The decoupling of the penalty.** -/
theorem pen_decouple {α : ℝ} (hα : 0 < α) (h0 x y ξ ζ : EuclSpace d) :
    penP (1 / 2) 1 α h0 (x - y)
      ≤ penP 1 2 α h0 (ξ - ζ) + lamC α h0 / 2 * (‖x - ξ‖ ^ 2 + ‖y - ζ‖ ^ 2) := by
  have e : x - y = (ξ - ζ) + ((x - ξ) - (y - ζ)) := by abel
  rw [e]
  set b := (x - ξ) - (y - ζ) with hb
  have hy := penP_young (s := 1 / 2) (r := 1) (h0 := h0) (by norm_num) zero_le_one hα
    one_pos (ξ - ζ) b
  have hle := penP_le (s := 1 / 2) (r := 1) (h0 := h0) (by norm_num) hα b
  have hsq := norm_sub_sq_le_two (x - ξ) (y - ζ)
  have hM0 := penM_nonneg (h0 := h0) (by norm_num : (0:ℝ) ≤ 1 / 2) zero_le_one hα
  have h2 : (1 + 1) * penP (1 / 2) 1 α h0 (ξ - ζ) = penP 1 2 α h0 (ξ - ζ) := by
    unfold penP; ring
  have p2 : penM (1 / 2) 1 α h0 * ‖b‖ ^ 2
      ≤ penM (1 / 2) 1 α h0 * (2 * (‖x - ξ‖ ^ 2 + ‖y - ζ‖ ^ 2)) :=
    mul_le_mul_of_nonneg_left hsq hM0
  have p3 : 0 ≤ ‖x - ξ‖ ^ 2 + ‖y - ζ‖ ^ 2 := by positivity
  unfold lamC
  norm_num at hy
  nlinarith

section conv

variable {uT vT : EuclSpace d → ℝ} {α : ℝ} {h0 : EuclSpace d}

/-- The doubled function is nonpositive everywhere. -/
theorem psi_nonpos (_hα : 0 < α) (hu0 : uT 0 = 0) (hv0 : vT 0 = 0)
    (hΨ : ∀ w : EuclSpace d × EuclSpace d, w ≠ 0 →
      uT w.1 - vT w.2 - penP (1 / 2) 1 α h0 (w.1 - w.2) < 0)
    (x y : EuclSpace d) :
    uT x - vT y ≤ penP (1 / 2) 1 α h0 (x - y) := by
  by_cases h : (x, y) = (0 : EuclSpace d × EuclSpace d)
  · have hx : x = 0 := congrArg Prod.fst h
    have hy : y = 0 := congrArg Prod.snd h
    subst hx; subst hy
    simp [hu0, hv0, penP_zero]
  · have := hΨ (x, y) h
    linarith

/-- **The convolutions are bounded by the doubled penalty.** -/
theorem supConv_sum_le (hα : 0 < α) (hu0 : uT 0 = 0) (hv0 : vT 0 = 0)
    (hΨ : ∀ w : EuclSpace d × EuclSpace d, w ≠ 0 →
      uT w.1 - vT w.2 - penP (1 / 2) 1 α h0 (w.1 - w.2) < 0)
    (ξ ζ : EuclSpace d) :
    supConv (lamC α h0) uT ξ + supConv (lamC α h0) (fun y => -vT y) ζ
      ≤ penP 1 2 α h0 (ξ - ζ) := by
  set L := lamC α h0
  have hdec : ∀ x y, uT x - L / 2 * ‖x - ξ‖ ^ 2 + (-vT y - L / 2 * ‖y - ζ‖ ^ 2)
      ≤ penP 1 2 α h0 (ξ - ζ) := by
    intro x y
    have h1 := psi_nonpos hα hu0 hv0 hΨ x y
    have h2 := pen_decouple (h0 := h0) hα x y ξ ζ
    linarith
  have hn : ∀ x, supConv L (fun y => -vT y) ζ
      ≤ penP 1 2 α h0 (ξ - ζ) - (uT x - L / 2 * ‖x - ξ‖ ^ 2) := by
    intro x
    apply ciSup_le
    intro y
    have := hdec x y
    linarith
  have hu : supConv L uT ξ ≤ penP 1 2 α h0 (ξ - ζ) - supConv L (fun y => -vT y) ζ := by
    apply ciSup_le
    intro x
    have := hn x
    linarith
  linarith

/-- **Both convolutions vanish at the origin.** -/
theorem supConv_zero (hα : 0 < α) (hu0 : uT 0 = 0) (hv0 : vT 0 = 0)
    (hub : BddAbove (range uT)) (hvb : BddAbove (range (fun y => -vT y)))
    (hΨ : ∀ w : EuclSpace d × EuclSpace d, w ≠ 0 →
      uT w.1 - vT w.2 - penP (1 / 2) 1 α h0 (w.1 - w.2) < 0) :
    supConv (lamC α h0) uT 0 = 0 ∧
      supConv (lamC α h0) (fun y => -vT y) 0 = 0 := by
  have hL := (lamC_pos hα h0).le
  have h1 := self_le_supConv hL hub 0
  have h2 := self_le_supConv hL hvb 0
  have h3 := supConv_sum_le hα hu0 hv0 hΨ (h0 := h0) 0 0
  rw [hu0] at h1
  simp only [hv0, neg_zero] at h2
  rw [sub_zero, penP_zero] at h3
  constructor <;> linarith

/-- **The convolved doubled function has a strict maximum at the origin.** -/
theorem dblW0_conv_strict (hα : 0 < α) (hu0 : uT 0 = 0) (hv0 : vT 0 = 0)
    (huu : UpperSemicontinuous uT) (hub : BddAbove (range uT))
    (hvv : UpperSemicontinuous (fun y => -vT y))
    (hvb : BddAbove (range (fun y => -vT y)))
    (hΨ : ∀ w : EuclSpace d × EuclSpace d, w ≠ 0 →
      uT w.1 - vT w.2 - penP (1 / 2) 1 α h0 (w.1 - w.2) < 0) :
    ∀ w : EuclSpace d × EuclSpace d, w ≠ 0 →
      dblW0 (supConv (lamC α h0) uT)
          (fun ζ => -supConv (lamC α h0) (fun y => -vT y) ζ) 1 2 α h0 w
        < dblW0 (supConv (lamC α h0) uT)
          (fun ζ => -supConv (lamC α h0) (fun y => -vT y) ζ) 1 2 α h0 0 := by
  intro w hw
  set L := lamC α h0 with hLdef
  have hLpos := lamC_pos hα h0
  obtain ⟨hz1, hz2⟩ := supConv_zero hα hu0 hv0 hub hvb hΨ
  -- the value at the origin is zero
  have h0val : dblW0 (supConv L uT) (fun ζ => -supConv L (fun y => -vT y) ζ)
      1 2 α h0 0 = 0 := by
    unfold dblW0
    simp only [Prod.fst_zero, Prod.snd_zero, sub_zero, penP_zero]
    rw [hz1, hz2, neg_zero, sub_zero]
  rw [h0val]
  -- attainment
  obtain ⟨xs, hxs⟩ := supConv_attained hLpos huu hub w.1
  obtain ⟨ys, hys⟩ := supConv_attained hLpos hvv hvb w.2
  unfold dblW0
  simp only
  rw [hxs, hys]
  change uT xs - L / 2 * ‖xs - w.1‖ ^ 2 - -(-vT ys - L / 2 * ‖ys - w.2‖ ^ 2)
    - penP 1 2 α h0 (w.1 - w.2) < 0
  by_cases hz : (xs, ys) = (0 : EuclSpace d × EuclSpace d)
  · -- both maximizers vanish
    have hx : xs = 0 := congrArg Prod.fst hz
    have hy : ys = 0 := congrArg Prod.snd hz
    subst hx; subst hy
    rw [hu0, hv0]
    simp only [zero_sub, norm_neg]
    have hw4 := sum_pow_four_pos hw
    have hpos : 0 < ‖w.1‖ ^ 2 + ‖w.2‖ ^ 2 := by
      by_contra hc
      push Not at hc
      have a1 : ‖w.1‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖w.1‖, sq_nonneg ‖w.2‖]
      have a2 : ‖w.2‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖w.1‖, sq_nonneg ‖w.2‖]
      have b1 : ‖w.1‖ = 0 := (pow_eq_zero_iff (by norm_num)).1 a1
      have b2 : ‖w.2‖ = 0 := (pow_eq_zero_iff (by norm_num)).1 a2
      rw [b1, b2] at hw4
      norm_num at hw4
    have hP := penP_nonneg (h0 := h0) zero_le_one (by norm_num : (0:ℝ) ≤ 2) hα (w.1 - w.2)
    nlinarith
  · -- otherwise Ψ < 0 at the maximizers
    have h1 := hΨ (xs, ys) hz
    have h2 := pen_decouple (h0 := h0) hα xs ys w.1 w.2
    simp only at h1
    linarith

/-- The first convolution is semiconvex. -/
theorem semiconvex_uconv (hα : 0 < α) (hub : BddAbove (range uT)) :
    SemiconvexWith (lamC α h0) (supConv (lamC α h0) uT) :=
  semiconvex_supConv (lamC_pos hα h0).le hub

/-- The negated second convolution is semiconvex. -/
theorem semiconvex_vconv (hα : 0 < α) (hvb : BddAbove (range (fun y => -vT y))) :
    SemiconvexWith (lamC α h0)
      (fun y => -(fun ζ => -supConv (lamC α h0) (fun y => -vT y) ζ) y) := by
  have h := semiconvex_supConv (lamC_pos hα h0).le hvb (lam := lamC α h0)
  unfold SemiconvexWith at h ⊢
  simp only [neg_neg]
  exact h

end conv

end

end PLaplacian
