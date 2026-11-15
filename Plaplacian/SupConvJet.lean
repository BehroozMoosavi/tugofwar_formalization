/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.CVJet

@[expose] public section

/-! # Sup-convolutions of subsolutions

The comparison argument works with the sup-convolution `u^λ = supConv λ u` of a
subsolution, and needs only the jet form of the subsolution inequality: at a
point `ξ` all of whose maximizers lie in `Ω`, every superjet of `u^λ` with
nonzero gradient satisfies `viscF ≤ 0`. This is the magic property
(`superJet_of_supConv`) followed by the jet bridge (`superJet_regular`) at the
maximizer.

Maximizers are close to `ξ`: comparing with the value at `ξ` itself,
`(λ/2)‖xs - ξ‖² ≤ sup u - u(ξ)`.
-/

open Set Topology Filter Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



section

variable {lam : ℝ} {u : EuclSpace d → ℝ}

/-- **Maximizers of the sup-convolution are close.** -/
theorem supConv_maximizer_close (hlam : 0 ≤ lam) (hub : BddAbove (range u)) {SU : ℝ}
    (hSU : ∀ x, u x ≤ SU) {ξ xs : EuclSpace d}
    (hxs : supConv lam u ξ = u xs - lam / 2 * ‖xs - ξ‖ ^ 2) :
    lam / 2 * ‖xs - ξ‖ ^ 2 ≤ SU - u ξ := by
  have h1 : u ξ - lam / 2 * ‖ξ - ξ‖ ^ 2 ≤ supConv lam u ξ :=
    le_ciSup (bddAbove_supConv_family hlam hub ξ) ξ
  rw [sub_self, norm_zero] at h1
  have h2 := hSU xs
  nlinarith

/-- **The jet form of the subsolution inequality for a sup-convolution.** -/
theorem supConv_jet (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p) {Ω : Set (EuclSpace d)}
    (hsub : IsViscositySubsolution p Ω (fun _ => 0) u) (hlam : 0 < lam)
    (hu : UpperSemicontinuous u) (hub : BddAbove (range u)) {ξ : EuclSpace d}
    (hξ : ∀ xs, supConv lam u ξ = u xs - lam / 2 * ‖xs - ξ‖ ^ 2 → xs ∈ Ω)
    {q : EuclSpace d} {X : Bilin d} (hj : (q, X) ∈ SuperJet (supConv lam u) ξ)
    (hq : q ≠ 0) : viscF p q X ≤ 0 := by
  obtain ⟨xs, hxs⟩ := supConv_attained hlam hu hub ξ
  exact superJet_regular hd hp hsub (hξ xs hxs) (superJet_of_supConv hlam.le hub hxs hj) hq

/-- **Maximizers lie in `Ω` when a ball around `ξ` does.** -/
theorem supConv_maximizer_mem (hlam : 0 < lam) (hub : BddAbove (range u)) {SU SL : ℝ}
    (hSU : ∀ x, u x ≤ SU) (hSL : ∀ x, SL ≤ u x) {Ω : Set (EuclSpace d)} {ξ : EuclSpace d}
    {ρ : ℝ} (hρ : 2 * (SU - SL) / lam < ρ ^ 2) (hρ0 : 0 < ρ) (hball : ball ξ ρ ⊆ Ω) :
    ∀ xs, supConv lam u ξ = u xs - lam / 2 * ‖xs - ξ‖ ^ 2 → xs ∈ Ω := by
  intro xs hxs
  apply hball
  rw [mem_ball, dist_eq_norm]
  have h1 := supConv_maximizer_close hlam.le hub hSU hxs
  have h2 := hSL ξ
  have h3 : ‖xs - ξ‖ ^ 2 ≤ 2 * (SU - SL) / lam := by
    rw [le_div_iff₀ hlam]
    nlinarith
  have h4 : ‖xs - ξ‖ ^ 2 < ρ ^ 2 := lt_of_le_of_lt h3 hρ
  exact lt_of_pow_lt_pow_left₀ 2 hρ0.le h4

end

end

end PLaplacian
