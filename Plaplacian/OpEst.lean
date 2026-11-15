/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.GradEst

@[expose] public section

/-! # Operator estimates, and jets at Alexandrov points

**The operator.** For `p ≥ 2`:

1. ellipticity: `A ≤ Y` as quadratic forms gives `Δᴺₚ(q, A) ≤ Δᴺₚ(q, Y)`;
2. `Δᴺₚ(q, Y + c I) = Δᴺₚ(q, Y) + c (d + p - 2)`;
3. continuity in the direction of the gradient: if `|Y(v, v)| ≤ L ‖v‖²`, then
   `|Δᴺₚ(a, Y) - Δᴺₚ(b, Y)| ≤ (p - 2) · 2L · 2|a - b|/|b|`, from
   `Yₛ(e, e) - Yₛ(f, f) = Yₛ(e - f, e) + Yₛ(f, e - f)` and
   `|â - b̂| ≤ 2|a - b|/|b|`.

**Jets.** A convex function's Peano Hessian is nonnegative; passing from
`U + (λ/2)‖·‖²` to `U`, and from `-V + (λ/2)‖·‖²` to `V`, gives Hessians
bounded below by `-λ` and above by `λ` respectively. Both passages are written
with subtraction only.
-/

open Set Topology Filter Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-! ## The operator -/

/-- **Ellipticity.** -/
theorem normPLapOf_mono {p : ℝ} (hp : 2 ≤ p) {A Y : Bilin d} (h : QuadLE A Y)
    (q : EuclSpace d) : normPLapOf p q A ≤ normPLapOf p q Y := by
  unfold normPLapOf infLaplacianOf laplacianOf
  have h1 : ∑ i : Fin d, (A (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single i 1)
      ≤ ∑ i : Fin d, (Y (EuclideanSpace.single i (1 : ℝ))) (EuclideanSpace.single i 1) :=
    Finset.sum_le_sum fun i _ => h _
  have h2 := mul_le_mul_of_nonneg_left (h (‖q‖⁻¹ • q)) (by linarith : (0 : ℝ) ≤ p - 2)
  linarith

/-- **Adding a multiple of the identity.** -/
theorem normPLapOf_add_id {p : ℝ} {q : EuclSpace d} (hq : q ≠ 0) (Y : Bilin d) (c : ℝ) :
    normPLapOf p q (Y + c • idForm d) = normPLapOf p q Y + c * ((d : ℝ) + p - 2) := by
  have hqn : 0 < ‖q‖ := norm_pos_iff.2 hq
  unfold normPLapOf infLaplacianOf
  rw [laplacianOf_add, laplacianOf_smul, laplacianOf_idForm, add_apply, add_apply,
    smul_apply, smul_apply, smul_eq_mul, idForm_apply]
  have h1 : ‖‖q‖⁻¹ • q‖ ^ 2 = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hqn.ne', one_pow]
  rw [h1]
  ring

/-- **Unit vectors in nearby directions are close.** -/
theorem unit_sub_le {a b : EuclSpace d} (ha : a ≠ 0) (hb : b ≠ 0) :
    ‖‖a‖⁻¹ • a - ‖b‖⁻¹ • b‖ ≤ 2 * ‖a - b‖ / ‖b‖ := by
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnb : 0 < ‖b‖ := norm_pos_iff.2 hb
  have e : ‖a‖⁻¹ • a - ‖b‖⁻¹ • b = (‖a‖⁻¹ - ‖b‖⁻¹) • a + ‖b‖⁻¹ • (a - b) := by
    rw [sub_smul, smul_sub]; abel
  rw [e]
  have k1 : ‖(‖a‖⁻¹ - ‖b‖⁻¹) • a‖ = |‖b‖ - ‖a‖| / ‖b‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have : ‖a‖⁻¹ - ‖b‖⁻¹ = (‖b‖ - ‖a‖) / (‖a‖ * ‖b‖) := by field_simp
    rw [this, abs_div, abs_of_pos (mul_pos hna hnb)]
    field_simp
  have k2 : ‖‖b‖⁻¹ • (a - b)‖ = ‖a - b‖ / ‖b‖ := by
    rw [norm_smul, norm_inv, norm_norm]
    field_simp
  have k3 : |‖b‖ - ‖a‖| ≤ ‖a - b‖ := by
    rw [abs_sub_comm]; exact abs_norm_sub_norm_le a b
  calc ‖(‖a‖⁻¹ - ‖b‖⁻¹) • a + ‖b‖⁻¹ • (a - b)‖
      ≤ ‖(‖a‖⁻¹ - ‖b‖⁻¹) • a‖ + ‖‖b‖⁻¹ • (a - b)‖ := norm_add_le _ _
    _ = |‖b‖ - ‖a‖| / ‖b‖ + ‖a - b‖ / ‖b‖ := by rw [k1, k2]
    _ ≤ ‖a - b‖ / ‖b‖ + ‖a - b‖ / ‖b‖ := by
        gcongr
    _ = 2 * ‖a - b‖ / ‖b‖ := by ring

/-- **The quadratic form at nearby unit vectors.** -/
theorem quad_unit_diff {Y : Bilin d} {L : ℝ} (hL : 0 ≤ L)
    (hY : ∀ v, |(Y v) v| ≤ L * ‖v‖ ^ 2) {e f : EuclSpace d} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) :
    |(Y e) e - (Y f) f| ≤ 2 * L * ‖e - f‖ := by
  rw [← symmForm_apply_self Y e, ← symmForm_apply_self Y f]
  have key : (symmForm Y e) e - (symmForm Y f) f
      = (symmForm Y (e - f)) e + (symmForm Y f) (e - f) := by
    rw [map_sub, sub_apply, map_sub]; ring
  rw [key]
  have h1 := symmForm_le_mul hL hY (e - f) e
  have h2 := symmForm_le_mul hL hY f (e - f)
  rw [he] at h1
  rw [hf] at h2
  calc |(symmForm Y (e - f)) e + (symmForm Y f) (e - f)|
      ≤ |(symmForm Y (e - f)) e| + |(symmForm Y f) (e - f)| := abs_add_le _ _
    _ ≤ L * ‖e - f‖ * 1 + L * 1 * ‖e - f‖ := add_le_add h1 h2
    _ = 2 * L * ‖e - f‖ := by ring

/-- **Continuity of the operator in the direction of the gradient.** -/
theorem normPLapOf_dir {p : ℝ} (hp : 2 ≤ p) {a b : EuclSpace d} (ha : a ≠ 0) (hb : b ≠ 0)
    {Y : Bilin d} {L : ℝ} (hL : 0 ≤ L) (hY : ∀ v, |(Y v) v| ≤ L * ‖v‖ ^ 2) :
    |normPLapOf p a Y - normPLapOf p b Y| ≤ (p - 2) * (2 * L * (2 * ‖a - b‖ / ‖b‖)) := by
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hnb : 0 < ‖b‖ := norm_pos_iff.2 hb
  unfold normPLapOf infLaplacianOf
  have hea : ‖‖a‖⁻¹ • a‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hna.ne']
  have heb : ‖‖b‖⁻¹ • b‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnb.ne']
  have h1 := quad_unit_diff hL hY hea heb
  have h2 := unit_sub_le ha hb
  have h3 : |(Y (‖a‖⁻¹ • a)) (‖a‖⁻¹ • a) - (Y (‖b‖⁻¹ • b)) (‖b‖⁻¹ • b)|
      ≤ 2 * L * (2 * ‖a - b‖ / ‖b‖) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
  have e : laplacianOf Y + (p - 2) * (Y (‖a‖⁻¹ • a)) (‖a‖⁻¹ • a)
      - (laplacianOf Y + (p - 2) * (Y (‖b‖⁻¹ • b)) (‖b‖⁻¹ • b))
      = (p - 2) * ((Y (‖a‖⁻¹ • a)) (‖a‖⁻¹ • a) - (Y (‖b‖⁻¹ • b)) (‖b‖⁻¹ • b)) := by ring
  rw [e, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ p - 2)]
  exact mul_le_mul_of_nonneg_left h3 (by linarith)

/-! ## Jets at Alexandrov points -/

/-- **A convex function's Peano Hessian is nonnegative.** -/
theorem convex_twiceDiff_nonneg {f : EuclSpace d → ℝ} (hf : ConvexOn ℝ univ f)
    {x g : EuclSpace d} {X : Bilin d} (h : TwiceDiffAt f x g X) (v : EuclSpace d) :
    0 ≤ (X v) v := by
  obtain ⟨hsup, hsub⟩ := h
  have hsg := convex_subJet_isSubgrad hf hsub
  by_contra hneg
  push Not at hneg
  set κ := -(X v) v with hκ
  have hκ0 : 0 < κ := by linarith
  set η := κ / (4 * (‖v‖ ^ 2 + 1)) with hηdef
  have hη : 0 < η := by positivity
  have hsup' : ∀ η > 0, ∀ᶠ y in 𝓝 x, f y ≤ f x + inner ℝ g (y - x)
      + 1 / 2 * (X (y - x)) (y - x) + η * ‖y - x‖ ^ 2 := hsup
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hsup' η hη)
  set t := ε / (2 * (‖v‖ + 1)) with ht
  have ht0 : 0 < t := by positivity
  have hdist : dist (x + t • v) x < ε := by
    rw [dist_eq_norm]
    have e : x + t • v - x = t • v := by abel
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, ht]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg v]
  have h1 := hball hdist
  have h2 : f x + inner ℝ g (x + t • v - x) ≤ f (x + t • v) := hsg (x + t • v)
  have e : x + t • v - x = t • v := by abel
  have hXt : (X (t • v)) (t • v) = t * (t * (X v) v) := by
    simp only [map_smul, smul_apply, smul_eq_mul]
  rw [e, hXt, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at h1
  rw [e] at h2
  -- 0 ≤ t² (½ X(v,v) + η ‖v‖²) < 0
  have h3 : 0 ≤ t ^ 2 * (1 / 2 * (X v) v + η * ‖v‖ ^ 2) := by nlinarith
  have h4 : η * ‖v‖ ^ 2 ≤ κ / 4 := by
    rw [hηdef, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg ‖v‖]
  have h5 : 1 / 2 * (X v) v + η * ‖v‖ ^ 2 < 0 := by linarith
  have h6 : t ^ 2 * (1 / 2 * (X v) v + η * ‖v‖ ^ 2) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) h5
  linarith

/-- **From `U + (λ/2)‖·‖²` back to `U`.** -/
theorem peanoAt_sub_halfsq {f : EuclSpace d → ℝ} {x g : EuclSpace d} {X : Bilin d}
    (h : PeanoAt f x g X) (lam : ℝ) :
    PeanoAt (fun y => f y - lam / 2 * ‖y‖ ^ 2) x (g - lam • x) (X - lam • idForm d) := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := h ε hε
  refine ⟨δ, hδ, fun k hk => ?_⟩
  have h1 := hb k hk
  change |(f (x + k) - lam / 2 * ‖x + k‖ ^ 2) - (f x - lam / 2 * ‖x‖ ^ 2)
    - inner ℝ (g - lam • x) k - 1 / 2 * ((X - lam • idForm d) k) k| ≤ ε * ‖k‖ ^ 2
  rw [inner_sub_left, real_inner_smul_left, sub_apply, sub_apply, smul_apply, smul_apply,
    smul_eq_mul, idForm_apply, norm_add_sq_real]
  have key : (f (x + k) - lam / 2 * (‖x‖ ^ 2 + 2 * inner ℝ x k + ‖k‖ ^ 2))
      - (f x - lam / 2 * ‖x‖ ^ 2) - (inner ℝ g k - lam * inner ℝ x k)
      - 1 / 2 * ((X k) k - lam * ‖k‖ ^ 2)
      = f (x + k) - f x - inner ℝ g k - 1 / 2 * (X k) k := by ring
  rw [key]
  exact h1

/-- **From `-V + (λ/2)‖·‖²` back to `V`.** -/
theorem peanoAt_halfsq_sub {f : EuclSpace d → ℝ} {x g : EuclSpace d} {X : Bilin d}
    (h : PeanoAt f x g X) (lam : ℝ) :
    PeanoAt (fun y => lam / 2 * ‖y‖ ^ 2 - f y) x (lam • x - g) (lam • idForm d - X) := by
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := h ε hε
  refine ⟨δ, hδ, fun k hk => ?_⟩
  have h1 := hb k hk
  change |(lam / 2 * ‖x + k‖ ^ 2 - f (x + k)) - (lam / 2 * ‖x‖ ^ 2 - f x)
    - inner ℝ (lam • x - g) k - 1 / 2 * ((lam • idForm d - X) k) k| ≤ ε * ‖k‖ ^ 2
  rw [inner_sub_left, real_inner_smul_left, sub_apply, sub_apply, smul_apply, smul_apply,
    smul_eq_mul, idForm_apply, norm_add_sq_real]
  have key : (lam / 2 * (‖x‖ ^ 2 + 2 * inner ℝ x k + ‖k‖ ^ 2) - f (x + k))
      - (lam / 2 * ‖x‖ ^ 2 - f x) - (lam * inner ℝ x k - inner ℝ g k)
      - 1 / 2 * (lam * ‖k‖ ^ 2 - (X k) k)
      = -(f (x + k) - f x - inner ℝ g k - 1 / 2 * (X k) k) := by ring
  rw [key, abs_neg]
  exact h1

end

end PLaplacian
