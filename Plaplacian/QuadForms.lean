/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.SupConv

/-! # Forms: the identity, symmetrization, and a norm bound

## The identity form

Shifting jets by `(λ/2)‖·‖²` needs `λ I` as a bilinear form. Building it from
the inner product as a continuous linear map runs into the semilinear form of
`innerSL`; instead it is taken as the second derivative of `½‖·‖²` at zero,
which is a bilinear form by construction, and its quadratic form is computed
along lines to be `‖v‖²`.

## Symmetrization

The forms produced by Alexandrov's theorem need not be symmetric, and their
antisymmetric part, invisible to every jet, could be unbounded, which would
defeat the compactness extraction. Symmetrizing, `Xˢ(u,w) = ½(X(u,w) + X(w,u))`,
keeps the quadratic form and hence the jet.

## The norm bound

For a symmetric form, polarization `4 S(u,w) = S(u+w,u+w) - S(u-w,u-w)` bounds
`|S(u,w)|` by `(L/2)(‖u‖² + ‖w‖²)` when `|S(v,v)| ≤ L ‖v‖²`; rescaling `u` and
`w` in opposite directions improves this to `L ‖u‖ ‖w‖`, so `‖S‖ ≤ L`.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-! ## The identity form -/

/-- **The identity form**, as the second derivative of `½‖·‖²`. -/
def idForm (d : ℕ) : Bilin d :=
  fderiv ℝ (fderiv ℝ (fun y : EuclSpace d => (1 / 2) * ‖y‖ ^ 2)) 0

theorem idForm_apply (v : EuclSpace d) : (idForm d v) v = ‖v‖ ^ 2 := by
  unfold idForm
  set ψ : EuclSpace d → ℝ := fun y => (1 / 2) * ‖y‖ ^ 2 with hψ
  have hc : ContDiff ℝ 2 ψ := contDiff_const.mul (contDiff_norm_sq ℝ)
  rw [← line_deriv_two hc 0 v]
  have hfun : (fun s : ℝ => ψ (0 + s • v))
      = fun s => 0 + s * 0 + s ^ 2 * ((1 / 2) * ‖v‖ ^ 2) := by
    funext s
    simp only [hψ, zero_add, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [hfun, deriv_deriv_quad_poly]
  ring

/-! ## Symmetrization -/

/-- **The symmetrization of a form.** -/
def symmForm (X : Bilin d) : Bilin d := (1 / 2 : ℝ) • (X + X.flip)

set_option synthInstance.maxHeartbeats 200000 in
-- Instance search on iterated continuous linear maps exceeds the default
-- budget when the scalar action and the sum are unfolded together.
theorem symmForm_apply (X : Bilin d) (u w : EuclSpace d) :
    (symmForm X u) w = (1 / 2) * ((X u) w + (X w) u) := by
  simp only [symmForm, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]

theorem symmForm_apply_self (X : Bilin d) (v : EuclSpace d) :
    (symmForm X v) v = (X v) v := by
  rw [symmForm_apply]; ring

theorem symmForm_comm (X : Bilin d) (u w : EuclSpace d) :
    (symmForm X u) w = (symmForm X w) u := by
  rw [symmForm_apply, symmForm_apply]; ring

/-- Symmetrization keeps a superjet. -/
theorem superJet_symmForm {u : EuclSpace d → ℝ} {x q : EuclSpace d}
    {X : Bilin d} (h : (q, X) ∈ SuperJet u x) :
    (q, symmForm X) ∈ SuperJet u x := by
  intro η hη
  filter_upwards [h η hη] with y hy
  change u y ≤ u x + inner ℝ q (y - x) + (1 / 2) * (symmForm X (y - x)) (y - x)
    + η * ‖y - x‖ ^ 2
  rw [symmForm_apply_self]
  exact hy

/-- Symmetrization keeps a subjet. -/
theorem subJet_symmForm {u : EuclSpace d → ℝ} {x q : EuclSpace d}
    {X : Bilin d} (h : (q, X) ∈ SubJet u x) :
    (q, symmForm X) ∈ SubJet u x := by
  intro η hη
  filter_upwards [h η hη] with y hy
  change u x + inner ℝ q (y - x) + (1 / 2) * (symmForm X (y - x)) (y - x)
    - η * ‖y - x‖ ^ 2 ≤ u y
  rw [symmForm_apply_self]
  exact hy

theorem quadLE_symmForm {X Y : Bilin d} (h : QuadLE X Y) :
    QuadLE (symmForm X) (symmForm Y) := by
  intro v
  rw [symmForm_apply_self, symmForm_apply_self]
  exact h v

/-! ## The norm bound -/

/-- Polarization for a symmetric form. -/
theorem polar_symmForm (X : Bilin d) (u w : EuclSpace d) :
    4 * (symmForm X u) w
      = (symmForm X (u + w)) (u + w) - (symmForm X (u - w)) (u - w) := by
  simp only [map_add, map_sub, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply]
  have h := symmForm_comm X u w
  ring_nf
  linarith

/-- The polarization bound. -/
theorem symmForm_le_half {X : Bilin d} {L : ℝ}
    (hX : ∀ v, |(X v) v| ≤ L * ‖v‖ ^ 2) (u w : EuclSpace d) :
    |(symmForm X u) w| ≤ L / 2 * (‖u‖ ^ 2 + ‖w‖ ^ 2) := by
  have hp := polar_symmForm X u w
  have h1 := hX (u + w)
  have h2 := hX (u - w)
  rw [← symmForm_apply_self X (u + w)] at h1
  rw [← symmForm_apply_self X (u - w)] at h2
  have hpar : ‖u + w‖ ^ 2 + ‖u - w‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖w‖ ^ 2) := by
    rw [norm_add_sq_real, norm_sub_sq_real]; ring
  have hparL : L * ‖u + w‖ ^ 2 + L * ‖u - w‖ ^ 2
      = L * (2 * (‖u‖ ^ 2 + ‖w‖ ^ 2)) := by rw [← hpar]; ring
  rw [abs_le] at h1 h2 ⊢
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  constructor <;> linarith

/-- **The rescaled bound**: `|Xˢ(u,w)| ≤ L ‖u‖ ‖w‖`. -/
theorem symmForm_le_mul {X : Bilin d} {L : ℝ} (_hL : 0 ≤ L)
    (hX : ∀ v, |(X v) v| ≤ L * ‖v‖ ^ 2) (u w : EuclSpace d) :
    |(symmForm X u) w| ≤ L * ‖u‖ * ‖w‖ := by
  by_cases hu : u = 0
  · subst hu; simp
  by_cases hw : w = 0
  · subst hw; simp
  have hnu : 0 < ‖u‖ := norm_pos_iff.2 hu
  have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw
  set t := Real.sqrt (‖w‖ / ‖u‖) with htdef
  have ht : 0 < t := Real.sqrt_pos.2 (div_pos hnw hnu)
  have ht2 : t ^ 2 = ‖w‖ / ‖u‖ := Real.sq_sqrt (div_pos hnw hnu).le
  -- the form is unchanged when u is scaled by t and w by 1/t
  have hscale : (symmForm X (t • u)) (t⁻¹ • w) = (symmForm X u) w := by
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    field_simp
  have hb := symmForm_le_half hX (t • u) (t⁻¹ • w)
  rw [hscale] at hb
  have e1 : ‖t • u‖ ^ 2 = ‖u‖ * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow, ht2]
    field_simp
  have e2 : ‖t⁻¹ • w‖ ^ 2 = ‖u‖ * ‖w‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht, mul_pow, inv_pow, ht2]
    field_simp
  rw [e1, e2] at hb
  linarith

/-- **The operator norm of a symmetrized form is bounded by its quadratic
bound.** -/
theorem norm_symmForm_le {X : Bilin d} {L : ℝ} (hL : 0 ≤ L)
    (hX : ∀ v, |(X v) v| ≤ L * ‖v‖ ^ 2) : ‖symmForm X‖ ≤ L := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ hL
  intro u w
  rw [Real.norm_eq_abs]
  exact symmForm_le_mul hL hX u w

end

end PLaplacian
