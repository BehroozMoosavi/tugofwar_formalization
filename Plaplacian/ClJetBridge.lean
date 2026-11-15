/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.JetBridge

@[expose] public section

/-! # The viscosity inequalities at closed jets

The theorem of sums produces closed jets: limits of jets at nearby points. The
inequalities at jets pass to their limits because the generators are
continuous where they are used --- the regular generator at a nonzero gradient,
and the lower envelope everywhere, being Lipschitz in the form.

Every limit is taken through an explicit bound by the operator norm of the
difference of forms, never through the topology of the space of continuous
linear maps; the closed jets are defined with norm convergence for exactly that
reason.

Also here: degenerate ellipticity in the quadratic-form order, and the sign of
the lower envelope at a nonpositive form, which together with the jet
inequalities are everything the comparison argument consumes.
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}



/-- A form applied twice to a vector of norm at most one is bounded by its
norm. -/
theorem norm_apply_apply_le {Z : Bilin d} {w : EuclSpace d} (hw : ‖w‖ ≤ 1) :
    ‖(Z w) w‖ ≤ ‖Z‖ := by
  have h0 : (0:ℝ) ≤ ‖w‖ := norm_nonneg w
  have hw2 : ‖w‖ * ‖w‖ ≤ 1 := by nlinarith
  calc ‖(Z w) w‖ ≤ ‖Z w‖ * ‖w‖ := (Z w).le_opNorm w
    _ ≤ (‖Z‖ * ‖w‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right (Z.le_opNorm w) h0
    _ = ‖Z‖ * (‖w‖ * ‖w‖) := by ring
    _ ≤ ‖Z‖ * 1 := mul_le_mul_of_nonneg_left hw2 (norm_nonneg Z)
    _ = ‖Z‖ := mul_one _

/-- **The quadratic form converges**, when the forms converge in norm and the
vectors converge within the unit ball. -/
theorem tendsto_quad {Xs : ℕ → Bilin d} {X : Bilin d}
    (hX : Tendsto (fun n => ‖Xs n - X‖) atTop (𝓝 0))
    {ws : ℕ → EuclSpace d} {w : EuclSpace d}
    (hw : Tendsto ws atTop (𝓝 w)) (hb : ∀ n, ‖ws n‖ ≤ 1) :
    Tendsto (fun n => (Xs n (ws n)) (ws n)) atTop (𝓝 ((X w) w)) := by
  have h1 : Tendsto (fun n => ((Xs n - X) (ws n)) (ws n)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => norm_apply_apply_le (hb n)) hX
  have h2 : Tendsto (fun n => (X (ws n)) (ws n)) atTop (𝓝 ((X w) w)) :=
    ((X.continuous.clm_apply continuous_id).tendsto w).comp hw
  have hsplit : (fun n => (Xs n (ws n)) (ws n))
      = fun n => ((Xs n - X) (ws n)) (ws n) + (X (ws n)) (ws n) := by
    funext n
    simp only [sub_apply]
    ring
  rw [hsplit]
  simpa using h1.add h2

/-- The unit normalization has norm at most one. -/
theorem norm_normalize_le (q : EuclSpace d) : ‖‖q‖⁻¹ • q‖ ≤ 1 := by
  by_cases hq : q = 0
  · simp [hq]
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hq)]

/-- The Laplacian converges. -/
theorem tendsto_laplacianOf {Xs : ℕ → Bilin d} {X : Bilin d}
    (hX : Tendsto (fun n => ‖Xs n - X‖) atTop (𝓝 0)) :
    Tendsto (fun n => laplacianOf (Xs n)) atTop (𝓝 (laplacianOf X)) := by
  unfold laplacianOf
  refine tendsto_finsetSum _ (fun i _ => ?_)
  exact tendsto_quad hX tendsto_const_nhds (fun _ => by simp)

/-- The infinity Laplacian converges at a nonzero limit gradient. -/
theorem tendsto_infLaplacianOf {Xs : ℕ → Bilin d} {X : Bilin d}
    (hX : Tendsto (fun n => ‖Xs n - X‖) atTop (𝓝 0))
    {qs : ℕ → EuclSpace d} {q : EuclSpace d} (hqs : Tendsto qs atTop (𝓝 q))
    (hq : q ≠ 0) :
    Tendsto (fun n => infLaplacianOf (qs n) (Xs n)) atTop
      (𝓝 (infLaplacianOf q X)) := by
  unfold infLaplacianOf
  have hn : ‖q‖ ≠ 0 := norm_ne_zero_iff.2 hq
  have hw : Tendsto (fun n => ‖qs n‖⁻¹ • qs n) atTop (𝓝 (‖q‖⁻¹ • q)) :=
    (hqs.norm.inv₀ hn).smul hqs
  exact tendsto_quad hX hw (fun n => norm_normalize_le (qs n))

/-- **The regular generator converges** at a nonzero limit gradient. -/
theorem tendsto_viscF {p : ℝ} {Xs : ℕ → Bilin d} {X : Bilin d}
    (hX : Tendsto (fun n => ‖Xs n - X‖) atTop (𝓝 0))
    {qs : ℕ → EuclSpace d} {q : EuclSpace d} (hqs : Tendsto qs atTop (𝓝 q))
    (hq : q ≠ 0) :
    Tendsto (fun n => viscF p (qs n) (Xs n)) atTop (𝓝 (viscF p q X)) := by
  have h := (tendsto_laplacianOf hX).add
    ((tendsto_infLaplacianOf hX hqs hq).const_mul (p - 2))
  simp only [viscF_eq_neg]
  unfold normPLapOf
  exact h.neg

/-- **The largest eigenvalue is Lipschitz** in the form. -/
theorem lamMax_le_add_norm (hd : 0 < d) (X Y : Bilin d) :
    lamMax X ≤ lamMax Y + ‖X - Y‖ := by
  unfold lamMax
  apply csSup_le ((sphere_nonempty hd).image _)
  rintro _ ⟨v, hv, rfl⟩
  have hv1 : ‖v‖ = 1 := hv
  change (X v) v ≤ _
  have h1 : (Y v) v ≤ sSup ((fun v => (Y v) v) '' {v : EuclSpace d | ‖v‖ = 1}) :=
    le_csSup (bddAbove_quad_sphere Y) ⟨v, hv, rfl⟩
  have h2 : ((X - Y) v) v ≤ ‖X - Y‖ :=
    le_trans (le_abs_self _)
      (by rw [← Real.norm_eq_abs]; exact norm_apply_apply_le (le_of_eq hv1))
  have h3 : (X v) v = (Y v) v + ((X - Y) v) v := by
    simp only [sub_apply]; ring
  linarith

/-- The same, with the difference reversed. Stated separately because the
subtraction on forms is not the generic one, so the reversal cannot be done by
rewriting. -/
theorem lamMax_le_add_norm' (hd : 0 < d) (X Y : Bilin d) :
    lamMax X ≤ lamMax Y + ‖Y - X‖ := by
  unfold lamMax
  apply csSup_le ((sphere_nonempty hd).image _)
  rintro _ ⟨v, hv, rfl⟩
  have hv1 : ‖v‖ = 1 := hv
  change (X v) v ≤ _
  have h1 : (Y v) v ≤ sSup ((fun v => (Y v) v) '' {v : EuclSpace d | ‖v‖ = 1}) :=
    le_csSup (bddAbove_quad_sphere Y) ⟨v, hv, rfl⟩
  have h2 : -(((Y - X) v) v) ≤ ‖Y - X‖ :=
    le_trans (neg_le_abs _)
      (by rw [← Real.norm_eq_abs]; exact norm_apply_apply_le (le_of_eq hv1))
  have h3 : (X v) v = (Y v) v - ((Y - X) v) v := by
    simp only [sub_apply]; ring
  linarith

theorem tendsto_lamMax (hd : 0 < d) {Xs : ℕ → Bilin d} {X : Bilin d}
    (hX : Tendsto (fun n => ‖Xs n - X‖) atTop (𝓝 0)) :
    Tendsto (fun n => lamMax (Xs n)) atTop (𝓝 (lamMax X)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hX
  rw [Real.norm_eq_abs, abs_le]
  have h1 := lamMax_le_add_norm hd (Xs n) X
  have h2 := lamMax_le_add_norm' hd X (Xs n)
  constructor <;> linarith

/-- **The lower envelope converges.** -/
theorem tendsto_viscFLower (hd : 0 < d) {p : ℝ} {Xs : ℕ → Bilin d}
    {X : Bilin d} (hX : Tendsto (fun n => ‖Xs n - X‖) atTop (𝓝 0)) :
    Tendsto (fun n => viscFLower p (Xs n)) atTop (𝓝 (viscFLower p X)) := by
  unfold viscFLower
  exact (tendsto_laplacianOf hX).neg.sub
    ((tendsto_lamMax hd hX).const_mul (p - 2))

/-- The lower envelope is below the regular generator, for `p ≥ 2`. -/
theorem viscFLower_le_viscF (hp : 2 ≤ p) {q : EuclSpace d} (hq : q ≠ 0)
    (X : Bilin d) : viscFLower p X ≤ viscF p q X := by
  rw [viscF_eq_neg]
  unfold viscFLower normPLapOf infLaplacianOf
  have hn : ‖‖q‖⁻¹ • q‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hq)]
  have h := quad_le_lamMax_norm X (‖q‖⁻¹ • q)
  rw [hn, one_pow, mul_one] at h
  have hp2 : (0:ℝ) ≤ p - 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h hp2]

/-- **Degenerate ellipticity**, in the quadratic-form order. -/
theorem viscF_anti (hp : 2 ≤ p) {X Y : Bilin d} (hXY : QuadLE X Y)
    (q : EuclSpace d) : viscF p q Y ≤ viscF p q X := by
  rw [viscF_eq_neg, viscF_eq_neg]
  unfold normPLapOf laplacianOf infLaplacianOf
  have hlap : ∑ i, (X (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1)
      ≤ ∑ i, (Y (EuclideanSpace.single i 1)) (EuclideanSpace.single i 1) :=
    Finset.sum_le_sum (fun i _ => hXY _)
  have hinf := hXY (‖q‖⁻¹ • q)
  have hp2 : (0:ℝ) ≤ p - 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hinf hp2]

/-- **At a nonpositive form the lower envelope is nonnegative.** -/
theorem viscFLower_nonneg_of_nonpos (hd : 0 < d) (hp : 2 ≤ p) {X : Bilin d}
    (hX : QuadLE X 0) : 0 ≤ viscFLower p X := by
  unfold viscFLower
  have hv : ∀ v, (X v) v ≤ 0 := fun v => by
    have := hX v; simpa using this
  have hlap : laplacianOf X ≤ 0 := by
    unfold laplacianOf
    exact Finset.sum_nonpos (fun i _ => hv _)
  have hlam : lamMax X ≤ 0 := by
    unfold lamMax
    apply csSup_le ((sphere_nonempty hd).image _)
    rintro _ ⟨v, _, rfl⟩
    exact hv v
  have hp2 : (0:ℝ) ≤ p - 2 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hlam hp2]

section closed

variable {p c : ℝ} {Ω : Set (EuclSpace d)} {u : EuclSpace d → ℝ}
  {x q : EuclSpace d} {X : Bilin d}

/-- **The regular subsolution inequality at a closed superjet.** -/
theorem clSuperJet_regular (hd : 0 < d) (hp : 2 ≤ p) (hΩ : IsOpen Ω)
    (hsub : IsViscositySubsolution p Ω (fun _ => c) u) (hx : x ∈ Ω)
    (hcl : (q, X) ∈ ClSuperJet u x) (hq : q ≠ 0) :
    viscF p q X ≤ c := by
  obtain ⟨xs, qs, Xs, hj, hxs, _, hqs, hXs⟩ := hcl
  have hxΩ : ∀ᶠ n in atTop, xs n ∈ Ω := hxs (hΩ.mem_nhds hx)
  have hqne : ∀ᶠ n in atTop, qs n ≠ 0 := hqs.eventually_ne hq
  have hineq : ∀ᶠ n in atTop, viscF p (qs n) (Xs n) ≤ c :=
    (hxΩ.and hqne).mono fun n hn =>
      superJet_regular hd hp hsub hn.1 (hj n) hn.2
  exact le_of_tendsto (tendsto_viscF hXs hqs hq) hineq

/-- **The singular subsolution inequality at a closed superjet.** -/
theorem clSuperJet_singular (hd : 0 < d) (hp : 2 ≤ p) (hΩ : IsOpen Ω)
    (hsub : IsViscositySubsolution p Ω (fun _ => c) u) (hx : x ∈ Ω)
    (hcl : (0, X) ∈ ClSuperJet u x) :
    viscFLower p X ≤ c := by
  obtain ⟨xs, qs, Xs, hj, hxs, _, _, hXs⟩ := hcl
  have hxΩ : ∀ᶠ n in atTop, xs n ∈ Ω := hxs (hΩ.mem_nhds hx)
  have hineq : ∀ᶠ n in atTop, viscFLower p (Xs n) ≤ c := by
    refine hxΩ.mono fun n hn => ?_
    by_cases hqn : qs n = 0
    · have hjn := hj n
      rw [hqn] at hjn
      exact superJet_singular hd hp hsub hn hjn
    · exact le_trans (viscFLower_le_viscF hp hqn (Xs n))
        (superJet_regular hd hp hsub hn (hj n) hqn)
  exact le_of_tendsto (tendsto_viscFLower hd hXs) hineq

/-- **The regular supersolution inequality at a closed subjet.** -/
theorem clSubJet_regular (hd : 0 < d) (hp : 2 ≤ p) (hΩ : IsOpen Ω)
    (hsup : IsViscositySupersolution p Ω (fun _ => c) u) (hx : x ∈ Ω)
    (hcl : (q, X) ∈ ClSubJet u x) (hq : q ≠ 0) :
    c ≤ viscF p q X := by
  obtain ⟨xs, qs, Xs, hj, hxs, _, hqs, hXs⟩ := hcl
  have hxΩ : ∀ᶠ n in atTop, xs n ∈ Ω := hxs (hΩ.mem_nhds hx)
  have hqne : ∀ᶠ n in atTop, qs n ≠ 0 := hqs.eventually_ne hq
  have hineq : ∀ᶠ n in atTop, c ≤ viscF p (qs n) (Xs n) :=
    (hxΩ.and hqne).mono fun n hn =>
      subJet_regular hd hp hsup hn.1 (hj n) hn.2
  exact ge_of_tendsto (tendsto_viscF hXs hqs hq) hineq

end closed

end

end PLaplacian
