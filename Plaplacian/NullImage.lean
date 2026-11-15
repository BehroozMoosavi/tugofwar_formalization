/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.Subgrad

@[expose] public section

/-! # Lipschitz images of null sets are null

A Lipschitz map of `EuclSpace d` to itself sends sets of measure zero to sets of
measure zero. Mathlib has the statement for Hausdorff measure, and the identity
of Hausdorff measure with volume on `Fin d → ℝ`, whose norm is the supremum
norm; the proof transfers through the continuous linear equivalence `L` of
the two spaces.

1. **Null sets cross a linear equivalence.** The pushforward of a Haar measure
   by a continuous linear equivalence is a Haar measure, and any two Haar
   measures are mutually absolutely continuous; so `L` and `L⁻¹` send null
   sets to null sets.
2. **On `Fin d → ℝ`**, Hausdorff measure is volume and a Lipschitz map increases
   it by at most `K^d`, so it sends null sets to null sets.
3. **Together**: `g = L ∘ J ∘ L⁻¹` is Lipschitz and `g(L N) = L(J N)`, so
   `L(J N)` is null, and so is `J N = L⁻¹(L(J N))`.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- **A continuous linear equivalence sends null sets to null sets**, for Haar
measures on finite-dimensional spaces. -/
theorem null_image_cle {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [FiniteDimensional ℝ F] (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure F) [ν.IsAddHaarMeasure] (L : E ≃L[ℝ] F) {s : Set E}
    (hs : μ s = 0) : ν (L '' s) = 0 := by
  have : (Measure.map L μ).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have hac : ν ≪ Measure.map L μ :=
    Measure.absolutelyContinuous_isAddHaarMeasure ν (Measure.map L μ)
  refine hac ?_
  have e := L.toHomeomorph.toMeasurableEquiv.map_apply (μ := μ) (L '' s)
  have hcoe : (⇑(L.toHomeomorph.toMeasurableEquiv) : E → F) = ⇑L := rfl
  rw [hcoe] at e
  rw [e, Set.preimage_image_eq _ L.injective]
  exact hs

/-- **On `Fin d → ℝ`, a Lipschitz map sends null sets to null sets.** -/
theorem null_image_pi_lipschitz {g : (Fin d → ℝ) → (Fin d → ℝ)} {K : NNReal}
    (hg : LipschitzWith K g) {A : Set (Fin d → ℝ)} (hA : volume A = 0) :
    volume (g '' A) = 0 := by
  have hH := hausdorffMeasure_pi_real (ι := Fin d)
  simp only [Fintype.card_fin] at hH
  rw [← hH] at hA ⊢
  have h := hg.hausdorffMeasure_image_le (d := (d : ℝ)) (Nat.cast_nonneg d) A
  rw [hA, mul_zero] at h
  exact le_antisymm h zero_le

/-- **A Lipschitz map of `EuclSpace d` sends null sets to null sets.** -/
theorem lipschitz_image_null {J : EuclSpace d → EuclSpace d} {K : NNReal}
    (hJ : LipschitzWith K J) {N : Set (EuclSpace d)}
    (hN : volume N = 0) : volume (J '' N) = 0 := by
  set L := EuclideanSpace.equiv (Fin d) ℝ with hLdef
  have hLN : volume (L '' N) = 0 := null_image_cle volume volume L hN
  have hLL : LipschitzWith ‖(L : EuclSpace d →L[ℝ] (Fin d → ℝ))‖₊ L :=
    (L : EuclSpace d →L[ℝ] (Fin d → ℝ)).lipschitzWith
  have hLs : LipschitzWith ‖(L.symm : (Fin d → ℝ) →L[ℝ] EuclSpace d)‖₊ L.symm :=
    (L.symm : (Fin d → ℝ) →L[ℝ] EuclSpace d).lipschitzWith
  have hg := hLL.comp (hJ.comp hLs)
  have h1 := null_image_pi_lipschitz hg hLN
  have himg : (⇑L ∘ (J ∘ ⇑L.symm)) '' (L '' N) = L '' (J '' N) := by
    rw [Set.image_image, Set.image_image]
    congr 1
  rw [himg] at h1
  have h2 := null_image_cle volume volume L.symm h1
  have e : L.symm '' (L '' (J '' N)) = J '' N := by
    rw [Set.image_image]
    simp
  rwa [e] at h2

end

end PLaplacian
