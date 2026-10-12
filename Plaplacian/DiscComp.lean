/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.PeanoUniq

/-! # Discrete comparison against a strict supersolution

1. If `u - v ≤ S` on `B_ε(x)`, then `T_ε u(x) - T_ε v(x) ≤ S`: the supremum, the
   infimum and the average each move by at most `S`, and the weights of the
   operator add to one.
2. On a bounded set `D`, let `u = T_ε u` and `T_ε v ≤ v - κ` on `D`, `κ > 0`, and
   `u ≤ v` at the points outside `D` within `ε` of it. Then `u ≤ v` on `D`.
   With `M = sup (u - v)` over the `ε`-neighbourhood of `D`: on `D`,
   `u - v ≤ M - κ`, and outside `D`, `u - v ≤ 0`; so `M ≤ max (M - κ) 0`,
   impossible when `M > 0`.
-/

open Set Topology Filter Metric MeasureTheory

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- **The operator moves by at most the supremum of the difference.** -/
theorem tugOfWarOp_diff_le {p ε : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ)) (hε : 0 < ε)
    {u v : EuclSpace d → ℝ} (hu : BddMeas u) (hv : BddMeas v) (x : EuclSpace d) {S : ℝ}
    (hS : ∀ y ∈ ball x ε, u y - v y ≤ S) :
    tugOfWarOp p ε u x - tugOfWarOp p ε v x ≤ S := by
  obtain ⟨Cu, hCu⟩ := hu.bound
  obtain ⟨Cv, hCv⟩ := hv.bound
  have hne : (ball x ε).Nonempty := ⟨x, mem_ball_self hε⟩
  have hvA : BddAbove (v '' ball x ε) := by
    refine ⟨Cv, ?_⟩
    rintro _ ⟨y, _, rfl⟩
    exact (abs_le.1 (hCv y)).2
  have huB : BddBelow (u '' ball x ε) := by
    refine ⟨-Cu, ?_⟩
    rintro _ ⟨y, _, rfl⟩
    exact (abs_le.1 (hCu y)).1
  -- the supremum
  have hsup : sSup (u '' ball x ε) ≤ S + sSup (v '' ball x ε) := by
    refine csSup_le (hne.image _) ?_
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hS y hy
    have h2 : v y ≤ sSup (v '' ball x ε) := le_csSup hvA ⟨y, hy, rfl⟩
    linarith
  -- the infimum
  have hinf : sInf (u '' ball x ε) ≤ S + sInf (v '' ball x ε) := by
    have : sInf (u '' ball x ε) - S ≤ sInf (v '' ball x ε) := by
      refine le_csInf (hne.image _) ?_
      rintro _ ⟨y, hy, rfl⟩
      have h1 := hS y hy
      have h2 : sInf (u '' ball x ε) ≤ u y := csInf_le huB ⟨y, hy, rfl⟩
      linarith
    linarith
  -- the average
  have hiu := hu.integrableOn_ball x ε
  have hiv := hv.integrableOn_ball x ε
  have havg : (⨍ y in ball x ε, u y) - (⨍ y in ball x ε, v y) ≤ S := by
    rw [← average_sub hiu hiv]
    have hconst : IntegrableOn (fun _ : EuclSpace d => S) (ball x ε) := integrableOn_const
    have h1 := setAverage_mono measurableSet_ball (hiu.sub hiv) hconst
      (fun y hy => hS y hy)
    rw [setAverage_const_ball S x hε] at h1
    exact h1
  -- the weights
  have hα : 0 ≤ (p - 2) / (p + (d : ℝ)) / 2 := by
    have : 0 ≤ p - 2 := by linarith
    positivity
  have hβ : 0 ≤ ((d : ℝ) + 2) / (p + (d : ℝ)) := by positivity
  have hαβ := alpha_add_beta (d := d) p hpd
  unfold tugOfWarOp
  have k1 := mul_le_mul_of_nonneg_left (add_le_add hsup hinf) hα
  have k2 := mul_le_mul_of_nonneg_left havg hβ
  have e : (p - 2) / (p + (d : ℝ)) / 2 * (S + S) + ((d : ℝ) + 2) / (p + (d : ℝ)) * S = S := by
    have : (p - 2) / (p + (d : ℝ)) / 2 * (S + S) = (p - 2) / (p + (d : ℝ)) * S := by ring
    rw [this, ← add_mul, hαβ, one_mul]
  nlinarith

/-- **Discrete comparison against a strict supersolution.** -/
theorem disc_comparison {p ε : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ)) (hε : 0 < ε)
    {D : Set (EuclSpace d)} {u v : EuclSpace d → ℝ} (hu : BddMeas u) (hv : BddMeas v)
    (hU : ∀ x ∈ D, u x = tugOfWarOp p ε u x)
    {κ : ℝ} (hκ : 0 < κ) (hV : ∀ x ∈ D, tugOfWarOp p ε v x ≤ v x - κ)
    (hstrip : ∀ w, w ∉ D → (∃ y ∈ D, dist w y < ε) → u w ≤ v w) :
    ∀ x ∈ D, u x ≤ v x := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x₀, hx₀D, hx₀⟩ := hcon
  obtain ⟨Cu, hCu⟩ := hu.bound
  obtain ⟨Cv, hCv⟩ := hv.bound
  -- the ε-neighbourhood of D, and the supremum of u - v over it
  set A := {w | ∃ y ∈ D, dist w y < ε} with hAdef
  have hx₀A : x₀ ∈ A := ⟨x₀, hx₀D, by rw [dist_self]; exact hε⟩
  have hbdd : BddAbove ((fun w => u w - v w) '' A) := by
    refine ⟨Cu + Cv, ?_⟩
    rintro _ ⟨w, _, rfl⟩
    have h1 := (abs_le.1 (hCu w)).2
    have h2 := (abs_le.1 (hCv w)).1
    change u w - v w ≤ Cu + Cv
    linarith
  set M := sSup ((fun w => u w - v w) '' A) with hM
  have hleM : ∀ w ∈ A, u w - v w ≤ M := fun w hw => le_csSup hbdd ⟨w, hw, rfl⟩
  have hMpos : 0 < M := by
    have := hleM x₀ hx₀A
    linarith
  -- every value is at most max (M - κ) 0
  have hbound : ∀ w ∈ A, u w - v w ≤ max (M - κ) 0 := by
    rintro w ⟨y, hyD, hwy⟩
    by_cases hwD : w ∈ D
    · -- on D: the difference drops by κ
      have hball : ∀ z ∈ ball w ε, u z - v z ≤ M := by
        intro z hz
        exact hleM z ⟨w, hwD, hz⟩
      have h1 := tugOfWarOp_diff_le hp hpd hε hu hv w hball
      have h2 := hU w hwD
      have h3 := hV w hwD
      have : u w - v w ≤ M - κ := by linarith
      exact le_trans this (le_max_left _ _)
    · -- outside D: u ≤ v
      have := hstrip w hwD ⟨y, hyD, hwy⟩
      exact le_trans (by linarith) (le_max_right _ _)
  have hMle : M ≤ max (M - κ) 0 := by
    refine csSup_le ⟨_, ⟨x₀, hx₀A, rfl⟩⟩ ?_
    rintro _ ⟨w, hw, rfl⟩
    exact hbound w hw
  rcases le_total (M - κ) 0 with h | h
  · rw [max_eq_right h] at hMle; linarith
  · rw [max_eq_left h] at hMle; linarith

end

end PLaplacian
