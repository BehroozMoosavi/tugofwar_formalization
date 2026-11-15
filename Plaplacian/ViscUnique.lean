/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.CompFull

@[expose] public section

/-!
# Uniqueness of viscosity solutions

Two bounded continuous viscosity solutions of `-Δₚᴺ u = 0` in a bounded open
set that agree on the boundary agree in the set. This is the comparison
principle `visc_comparison`, applied in both directions.

## Main result

- `visc_unique`
-/

/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/



open Set

namespace PLaplacian

variable {d : ℕ}

/-- **Uniqueness of viscosity solutions.** Two bounded continuous viscosity
solutions of the homogeneous normalized `p`-Laplace equation in a bounded open
set `Ω`, equal on `frontier Ω`, are equal in `Ω`. -/
theorem visc_unique (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p)
    {Ω : Set (EuclSpace d)} (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {u₁ u₂ : EuclSpace d → ℝ}
    (h₁c : Continuous u₁) (h₂c : Continuous u₂)
    (h₁a : BddAbove (range u₁)) (h₁b : BddBelow (range u₁))
    (h₂a : BddAbove (range u₂)) (h₂b : BddBelow (range u₂))
    (h₁sub : IsViscositySubsolution p Ω (fun _ => 0) u₁)
    (h₁sup : IsViscositySupersolution p Ω (fun _ => 0) u₁)
    (h₂sub : IsViscositySubsolution p Ω (fun _ => 0) u₂)
    (h₂sup : IsViscositySupersolution p Ω (fun _ => 0) u₂)
    (hbd : ∀ x ∈ frontier Ω, u₁ x = u₂ x) :
    ∀ x ∈ Ω, u₁ x = u₂ x := by
  intro x hx
  apply le_antisymm
  · exact visc_comparison hd hp hΩo hΩb h₁c.upperSemicontinuous
      h₂c.lowerSemicontinuous h₁a h₁b h₂b h₂a h₁sub h₂sup
      (fun y hy => (hbd y hy).le) x hx
  · exact visc_comparison hd hp hΩo hΩb h₂c.upperSemicontinuous
      h₁c.lowerSemicontinuous h₂a h₂b h₁b h₁a h₂sub h₁sup
      (fun y hy => (hbd y hy).ge) x hx

end PLaplacian
