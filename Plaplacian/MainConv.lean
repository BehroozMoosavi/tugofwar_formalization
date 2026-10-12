/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.BdryEst

/-! # Convergence of `p`-harmonious functions

Let `Ω ⊂ ℝᵈ` be bounded and open, with an exterior sphere at every boundary
point, and `F` continuous. Let `u_ε` be uniformly bounded, `p`-harmonious in `Ω`
with data `F`, and equal to `F` outside `Ω`. Then the relaxed limits coincide
on `Ω̄`, equal `F` on `∂Ω`, and `u_ε → ubar u` uniformly on `Ω̄`.

1. `ubar u ≤ F` on `∂Ω` is the boundary estimate; `F ≤ lbar u` is the same
   estimate for `-u_ε`, `p`-harmonious with data `-F`.
2. `ubar u` is a subsolution and `lbar u` a supersolution, so the comparison
   principle gives `ubar u ≤ lbar u` in `Ω`; with `lbar ≤ ubar`, they are equal.
3. On `∂Ω` both equal `F`, so they agree on `Ω̄ = Ω ∪ ∂Ω`.
4. A sequence of points where `|u_ε - ubar u|` stays above `η` has a subsequence
   converging to `x* ∈ Ω̄`; there the relaxed limits and the semicontinuity of
   `ubar` and `lbar` put both `u_ε` and `ubar u` within `η/3` of
   `ubar u x* = lbar u x*`.
-/

open Set Topology Filter Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



set_option maxHeartbeats 1600000 in
-- Comparison, the boundary estimates, and a compactness argument.
/-- **Convergence of `p`-harmonious functions to the viscosity solution.** -/
theorem pharmonious_converge [Nontrivial (EuclSpace d)] (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {F : EuclSpace d → ℝ} (hFc : Continuous F)
    (hext : ∀ y ∈ frontier Ω, ∃ (z : EuclSpace d) (δ : ℝ), 0 < δ ∧ ‖y - z‖ = δ ∧
      ∀ x ∈ Ω, δ ≤ ‖x - z‖)
    {u : ℝ → EuclSpace d → ℝ} {C : ℝ} (hC : ∀ ε y, |u ε y| ≤ C)
    (hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε))
    (hout : ∀ ε > 0, ∀ x, x ∉ Ω → u ε x = F x) :
    (∀ x ∈ closure Ω, ubar u x = lbar u x) ∧
    (∀ x ∈ frontier Ω, ubar u x = F x) ∧
    (∀ η > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → ∀ x ∈ closure Ω,
      |u ε x - ubar u x| ≤ η) := by
  -- the negated family
  have hC' : ∀ ε y, |(fun ε y => -u ε y) ε y| ≤ C := fun ε y => by
    simp only [abs_neg]; exact hC ε y
  have hu' : ∀ ε > 0, IsPHarmonious p ε Ω (fun y => -F y) ((fun ε y => -u ε y) ε) :=
    fun ε hε => isPHarmonious_neg (hu ε hε)
  have hout' : ∀ ε > 0, ∀ x, x ∉ Ω → (fun ε y => -u ε y) ε x = (fun y => -F y) x := by
    intro ε hε x hx
    change -u ε x = -F x
    rw [hout ε hε x hx]
  -- the bounds on the relaxed limits
  have hubC : ∀ x, ubar u x ≤ C := fun x =>
    ubar_le_of_bound u hC (S := Ioi 0) self_mem_nhdsWithin (V := univ) (b := C)
      (fun ε _ y _ => (abs_le.1 (hC ε y)).2) univ_mem
  have hlbC : ∀ x, -C ≤ lbar u x := by
    intro x
    have h : ubar (fun ε y => -u ε y) x ≤ C :=
      ubar_le_of_bound _ hC' (S := Ioi 0) self_mem_nhdsWithin (V := univ) (b := C)
        (fun ε _ y _ => (abs_le.1 (hC' ε y)).2) univ_mem
    rw [lbar_eq_neg_ubar_neg]
    linarith
  have hord : ∀ x, lbar u x ≤ ubar u x := lbar_le_ubar u hC
  -- the boundary estimates
  have hupper : ∀ y ∈ frontier Ω, ubar u y ≤ F y := by
    intro y hy
    obtain ⟨z, δ, hδ, hyz, hext'⟩ := hext y hy
    exact ubar_le_bdry hd hp hpd hC hu hout hFc.continuousAt hδ hyz hext'
  have hlower : ∀ y ∈ frontier Ω, F y ≤ lbar u y := by
    intro y hy
    obtain ⟨z, δ, hδ, hyz, hext'⟩ := hext y hy
    have h : ubar (fun ε y => -u ε y) y ≤ -F y :=
      ubar_le_bdry hd hp hpd hC' hu' hout' hFc.neg.continuousAt hδ hyz hext'
    rw [lbar_eq_neg_ubar_neg]
    linarith
  -- comparison in Ω
  have hcomp := visc_comparison hd hp hΩo hΩb (upperSemicontinuous_ubar u hC)
    (lowerSemicontinuous_lbar u hC)
    ⟨C, by rintro _ ⟨x, rfl⟩; exact hubC x⟩
    ⟨-C, by rintro _ ⟨x, rfl⟩; exact le_trans (hlbC x) (hord x)⟩
    ⟨-C, by rintro _ ⟨x, rfl⟩; exact hlbC x⟩
    ⟨C, by rintro _ ⟨x, rfl⟩; exact le_trans (hord x) (hubC x)⟩
    (ubar_isViscositySubsolution hd hp hpd hΩo hC hu)
    (lbar_isViscositySupersolution hd hp hpd hΩo hC hu)
    (fun x hx => le_trans (hupper x hx) (hlower x hx))
  -- the relaxed limits agree on the closure
  have heq : ∀ x ∈ closure Ω, ubar u x = lbar u x := by
    intro x hx
    rw [closure_eq_self_union_frontier] at hx
    rcases hx with hx | hx
    · exact le_antisymm (hcomp x hx) (hord x)
    · exact le_antisymm (le_trans (hupper x hx) (hlower x hx)) (hord x)
  have heqF : ∀ x ∈ frontier Ω, ubar u x = F x := fun x hx =>
    le_antisymm (hupper x hx) (le_trans (hlower x hx) (hord x))
  refine ⟨heq, heqF, ?_⟩
  -- uniform convergence, by contradiction
  intro η hη
  by_contra hcon
  push Not at hcon
  have hseq : ∀ n : ℕ, ∃ ε x, 0 < ε ∧ ε < 1 / ((n : ℝ) + 1) ∧ x ∈ closure Ω ∧
      η < |u ε x - ubar u x| := by
    intro n
    obtain ⟨ε, hε0, hε1, x, hx, hbad⟩ := hcon (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨ε, x, hε0, hε1, hx, hbad⟩
  choose εs xs hεs0 hεs1 hxs hbad using hseq
  -- a convergent subsequence
  obtain ⟨xstar, hxstar, φ, hφ, hxT⟩ := tendsto_subseq_of_bounded hΩb.closure hxs
  rw [closure_closure] at hxstar
  have hεT : Tendsto (fun n => εs (φ n)) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Eventually.of_forall fun n => hεs0 (φ n)⟩
    have h1 : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    exact squeeze_zero (fun n => (hεs0 (φ n)).le) (fun n => (hεs1 (φ n)).le) h1
  have hqT : Tendsto (fun n => (εs (φ n), xs (φ n))) atTop (relaxFilter xstar) :=
    hεT.prodMk hxT
  -- four eventual bounds at x*
  have hb : 0 < η / 3 := by positivity
  have e1 : ∀ᶠ n in atTop, u (εs (φ n)) (xs (φ n)) < ubar u xstar + η / 3 :=
    hqT.eventually (eventually_lt_of_ubar_lt u hC xstar (by linarith))
  have e2 : ∀ᶠ n in atTop, -u (εs (φ n)) (xs (φ n)) < -lbar u xstar + η / 3 := by
    have h : ubar (fun ε y => -u ε y) xstar < -lbar u xstar + η / 3 := by
      rw [lbar_eq_neg_ubar_neg]; linarith
    exact hqT.eventually (eventually_lt_of_ubar_lt _ hC' xstar h)
  have e3 : ∀ᶠ n in atTop, ubar u (xs (φ n)) < ubar u xstar + η / 3 :=
    hxT.eventually (upperSemicontinuous_ubar u hC xstar _ (by linarith))
  have e4 : ∀ᶠ n in atTop, lbar u xstar - η / 3 < lbar u (xs (φ n)) :=
    hxT.eventually (lowerSemicontinuous_lbar u hC xstar _ (by linarith))
  obtain ⟨n, h1, h2, h3, h4⟩ := (e1.and (e2.and (e3.and e4))).exists
  have h5 := heq (xs (φ n)) (hxs (φ n))
  have h6 := heq xstar hxstar
  have h7 := hbad (φ n)
  have : |u (εs (φ n)) (xs (φ n)) - ubar u (xs (φ n))| < η := by
    rw [abs_lt]; constructor <;> linarith
  linarith

end

end PLaplacian
