/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.MainConv
public import Plaplacian.DppOperator
public import Plaplacian.LimitMeas
public import Plaplacian.DeficitMono
public import Plaplacian.DomainBounds
public import Plaplacian.UniformLimit
public import Plaplacian.IndexSelection
public import Plaplacian.Dominated
public import Plaplacian.Bounds
public import Plaplacian.UniformIteration
public import Plaplacian.Discharge
public import Plaplacian.Selection

@[expose] public section

/-!
# Existence for the `ε`-problem with exterior data, and unconditional convergence

The Perron iteration of `Plaplacian.Iteration` applies `tugOfWarOp` at every
point, so it does not keep the exterior data fixed, and its uniform-convergence
estimate controls the deficit only on `closureEps Ω ε`. Here we iterate the
restricted operator `dppOp` instead: every iterate then equals the starting
function outside `Ω`, the deficit vanishes there, and the estimate of
Luiro--Parviainen--Saksman gives uniform convergence on all of `ℝᵈ`.

Starting from `F` outside `Ω` and `-C` on `Ω`, where `|F| ≤ C`, the limit is a
`p`-harmonious function with data `F` that equals `F` outside `Ω` and is bounded
by `C`. Feeding these functions to `pharmonious_converge` removes its standing
hypothesis that such a family exists.

## Main results

- `dirIter`, `dirLimit`: the iteration of `dppOp` and its limit.
- `dirIter_unif`: the iteration converges uniformly on `ℝᵈ`.
- `dirLimit_fixed`: the limit is a fixed point of `dppOp`.
- `exists_pharmonious`: existence for the `ε`-problem with exterior data `F`.
- `pharmonious_exists_converge`: existence and uniform convergence together.
-/

/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/



open MeasureTheory Metric Set Filter Topology

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! ### The iteration of the restricted operator -/

/-- The Perron iteration of the restricted operator: `u₀` given,
`u_{j+1} = dppOp u_j`. -/
def dirIter (p ε : ℝ) (Ω : Set (EuclSpace d)) (u₀ : EuclSpace d → ℝ) :
    ℕ → (EuclSpace d → ℝ)
  | 0 => u₀
  | (j+1) => dppOp p ε Ω (dirIter p ε Ω u₀ j)

@[simp] lemma dirIter_zero (p ε : ℝ) (Ω : Set (EuclSpace d))
    (u₀ : EuclSpace d → ℝ) : dirIter p ε Ω u₀ 0 = u₀ := rfl

@[simp] lemma dirIter_succ (p ε : ℝ) (Ω : Set (EuclSpace d))
    (u₀ : EuclSpace d → ℝ) (j : ℕ) :
    dirIter p ε Ω u₀ (j+1) = dppOp p ε Ω (dirIter p ε Ω u₀ j) := rfl

/-- The restricted operator preserves a bound. -/
theorem abs_dppOp_le (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ)) (Ω : Set (EuclSpace d))
    {v : EuclSpace d → ℝ} (hv : BddMeas v) {C : ℝ} (hC : ∀ y, |v y| ≤ C)
    (x : EuclSpace d) : |dppOp p ε Ω v x| ≤ C := by
  by_cases hx : x ∈ Ω
  · rw [dppOp_of_mem p ε hx]
    exact abs_tugOfWarOp_le p ε hp hε hpd hv hC x
  · rw [dppOp_of_notMem p ε hx]
    exact hC x

theorem bddMeas_dirIter (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} (hΩm : MeasurableSet Ω)
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) (j : ℕ) :
    BddMeas (dirIter p ε Ω u₀ j) := by
  induction j with
  | zero => exact hu₀
  | succ n ih => exact BddMeas.dppOp p ε hp hε hpd hΩm ih

theorem abs_dirIter_le (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} (hΩm : MeasurableSet Ω)
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C) (j : ℕ) :
    ∀ x, |dirIter p ε Ω u₀ j x| ≤ C := by
  induction j with
  | zero => exact hC
  | succ n ih =>
      intro x
      exact abs_dppOp_le p ε hp hε hpd Ω
        (bddMeas_dirIter p ε hp hε hpd hΩm hu₀ n) ih x

/-- From a subsolution of the restricted operator the iteration increases. -/
theorem dirIter_mono (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} (hΩm : MeasurableSet Ω)
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀)
    (hstep : ∀ x, u₀ x ≤ dppOp p ε Ω u₀ x) (j : ℕ) :
    ∀ x, dirIter p ε Ω u₀ j x ≤ dirIter p ε Ω u₀ (j+1) x := by
  induction j with
  | zero => exact hstep
  | succ n ih =>
      intro x
      exact dppOp_monotone p ε hp hd hε Ω
        (bddMeas_dirIter p ε hp hε hpd hΩm hu₀ n)
        (bddMeas_dirIter p ε hp hε hpd hΩm hu₀ (n+1)) ih x

/-- **The exterior data is never moved.** -/
theorem dirIter_eq_of_notMem (p ε : ℝ) {Ω : Set (EuclSpace d)}
    {u₀ : EuclSpace d → ℝ} {x : EuclSpace d} (hx : x ∉ Ω) (j : ℕ) :
    dirIter p ε Ω u₀ j x = u₀ x := by
  induction j with
  | zero => rfl
  | succ n ih => rw [dirIter_succ, dppOp_of_notMem p ε hx, ih]

theorem monotone_dirIter (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} (hΩm : MeasurableSet Ω)
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀)
    (hstep : ∀ x, u₀ x ≤ dppOp p ε Ω u₀ x) (x : EuclSpace d) :
    Monotone (fun j => dirIter p ε Ω u₀ j x) :=
  monotone_nat_of_le_succ fun n =>
    dirIter_mono p ε hp hε hd hpd hΩm hu₀ hstep n x

/-- The limit of the iteration, as the pointwise supremum. -/
def dirLimit (p ε : ℝ) (Ω : Set (EuclSpace d)) (u₀ : EuclSpace d → ℝ)
    (x : EuclSpace d) : ℝ :=
  ⨆ j, dirIter p ε Ω u₀ j x

theorem bddAbove_dirIter (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} (hΩm : MeasurableSet Ω)
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C) (x : EuclSpace d) :
    BddAbove (Set.range fun j => dirIter p ε Ω u₀ j x) := by
  refine ⟨C, ?_⟩
  rintro a ⟨j, rfl⟩
  exact (abs_le.1 (abs_dirIter_le p ε hp hε hpd hΩm hu₀ hC j x)).2

theorem tendsto_dirIter (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} (hΩm : MeasurableSet Ω)
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C)
    (hstep : ∀ x, u₀ x ≤ dppOp p ε Ω u₀ x) (x : EuclSpace d) :
    Tendsto (fun j => dirIter p ε Ω u₀ j x) atTop
      (𝓝 (dirLimit p ε Ω u₀ x)) :=
  tendsto_atTop_ciSup (monotone_dirIter p ε hp hε hd hpd hΩm hu₀ hstep x)
    (bddAbove_dirIter p ε hp hε hpd hΩm hu₀ hC x)

theorem dirIter_le_dirLimit (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} (hΩm : MeasurableSet Ω)
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C) (j : ℕ) (x : EuclSpace d) :
    dirIter p ε Ω u₀ j x ≤ dirLimit p ε Ω u₀ x :=
  le_ciSup (bddAbove_dirIter p ε hp hε hpd hΩm hu₀ hC x) j

theorem abs_dirLimit_le (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} (hΩm : MeasurableSet Ω)
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C) (x : EuclSpace d) :
    |dirLimit p ε Ω u₀ x| ≤ C := by
  have hlo : -C ≤ dirLimit p ε Ω u₀ x := by
    have h0 := dirIter_le_dirLimit p ε hp hε hpd hΩm hu₀ hC 0 x
    simp only [dirIter_zero] at h0
    linarith [(abs_le.1 (hC x)).1]
  have hhi : dirLimit p ε Ω u₀ x ≤ C := by
    unfold dirLimit
    refine ciSup_le fun i => ?_
    exact (abs_le.1 (abs_dirIter_le p ε hp hε hpd hΩm hu₀ hC i x)).2
  rw [abs_le]
  exact ⟨hlo, hhi⟩

theorem bddMeas_dirLimit (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} (hΩm : MeasurableSet Ω)
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C)
    (hstep : ∀ x, u₀ x ≤ dppOp p ε Ω u₀ x) :
    BddMeas (dirLimit p ε Ω u₀) := by
  refine ⟨?_, ⟨C, abs_dirLimit_le p ε hp hε hpd hΩm hu₀ hC⟩⟩
  refine measurable_of_tendsto_metrizable
    (f := fun j => dirIter p ε Ω u₀ j) ?_ ?_
  · exact fun j => (bddMeas_dirIter p ε hp hε hpd hΩm hu₀ j).meas
  · rw [tendsto_pi_nhds]
    exact fun x => tendsto_dirIter p ε hp hε hd hpd hΩm hu₀ hC hstep x

/-- The limit equals the starting function outside `Ω`. -/
theorem dirLimit_eq_of_notMem (p ε : ℝ) {Ω : Set (EuclSpace d)}
    {u₀ : EuclSpace d → ℝ} {x : EuclSpace d} (hx : x ∉ Ω) :
    dirLimit p ε Ω u₀ x = u₀ x := by
  unfold dirLimit
  simp only [dirIter_eq_of_notMem p ε hx]
  exact ciSup_const

/-! ### The estimate of Luiro--Parviainen--Saksman, for a general sequence

This is `deficitLimit_eq_zero` with the iteration replaced by an arbitrary
increasing sequence below its limit; the proof is unchanged. -/

theorem deficit_le_zero_gen (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)}
    {u : EuclSpace d → ℝ} {w : ℕ → EuclSpace d → ℝ} {C : ℝ}
    (hBMu : BddMeas u) (hBM : ∀ j, BddMeas (w j))
    (hle : ∀ j y, w j y ≤ u y)
    (hCd : ∀ j y, |u y - w j y| ≤ C)
    (hnn : ∀ j y, 0 ≤ u y - w j y)
    {M : ℝ}
    (hglob : ∀ η > 0, ∀ δ' > 0, ∃ k, (∫ y in closureEps Ω ε,
      (u y - w k y)) ≤ η
      ∧ deficitSup (closureEps Ω ε) u (w k) ≤ M + δ')
    (hint : ∀ k, MeasureTheory.IntegrableOn
      (fun y => u y - w k y) (closureEps Ω ε))
    (hsel : ∀ (δ : ℝ), 0 < δ → ∀ k : ℕ, ∃ x₀ ∈ Ω, ∃ l : ℕ,
      M - 2 * δ ≤ tugOfWarOp p ε (w l) x₀ - tugOfWarOp p ε (w k) x₀) :
    M ≤ 0 := by
  have hα : (0 : ℝ) ≤ (p - 2) / (p + (d : ℝ)) :=
    div_nonneg (by linarith) hpd.le
  have hβ : (0 : ℝ) < ((d : ℝ) + 2) / (p + (d : ℝ)) := by positivity
  have hvol : (0 : ℝ) < volume.real (ball (0 : EuclSpace d) ε) := by
    have h1 : volume (ball (0 : EuclSpace d) ε) ≠ 0 :=
      measure_ball_ne_zero 0 hε
    have h2 : volume (ball (0 : EuclSpace d) ε) ≠ ⊤ := measure_ball_lt_top.ne
    simp only [MeasureTheory.Measure.real]
    exact ENNReal.toReal_pos h1 h2
  refine deficitLimit_le_zero hα hβ (alpha_add_beta p hpd) ?_
  intro δ hδ
  set η := δ * volume.real (ball (0 : EuclSpace d) ε)
    / (((d : ℝ) + 2) / (p + (d : ℝ))) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]; positivity
  have hηeq : ((d : ℝ) + 2) / (p + (d : ℝ))
      * ((volume.real (ball (0 : EuclSpace d) ε))⁻¹ * η) = δ := by
    rw [hηdef]
    field_simp
  obtain ⟨k, hksmall, hksup⟩ := hglob η hηpos δ hδ
  obtain ⟨x₀, hx₀Ω, l, hchain⟩ := hsel δ hδ k
  refine ⟨⨍ y in ball x₀ ε, (u y - w k y),
          sSup ((fun y => u y - w k y) '' ball x₀ ε),
          ?_, ?_, ?_⟩
  · refine le_trans hchain ?_
    exact bound_one p ε hp hε hpd hBMu (hBM l) (hBM k)
      (fun y => hle l y) (hCd k) x₀
  · exact bound_two (hCd k) hksup hx₀Ω hε
  · rw [← hηeq]
    exact bound_three hε (hnn k) (hint k) hx₀Ω hβ.le hksmall

/-! ### Uniform convergence on all of `ℝᵈ` -/

/-- A bounded measurable function is integrable on a set of finite measure. -/
theorem integrableOn_of_bddMeas {v : EuclSpace d → ℝ} (hv : BddMeas v)
    {S : Set (EuclSpace d)} (hSfin : volume S ≠ ⊤) :
    MeasureTheory.IntegrableOn v S := by
  obtain ⟨D, hD⟩ := hv.bound
  have hconst : MeasureTheory.IntegrableOn
      (fun _ : EuclSpace d => D) S := by
    refine MeasureTheory.integrableOn_const ?_ ?_
    · exact hSfin
    · simp
  exact hconst.mono' hv.meas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by simpa using hD y)

/-- If the deficit vanishes outside `Ω`, its supremum over any set is at most
its supremum over `Ω`. -/
theorem deficitSup_le_of_vanish {Ω S : Set (EuclSpace d)} (hΩn : Ω.Nonempty)
    (hS : S.Nonempty) {u w : EuclSpace d → ℝ} {C : ℝ}
    (hC : ∀ x, |u x - w x| ≤ C) (hnn : ∀ x, 0 ≤ u x - w x)
    (hoff : ∀ x, x ∉ Ω → u x - w x = 0) :
    deficitSup S u w ≤ deficitSup Ω u w := by
  unfold deficitSup
  refine csSup_le (hS.image _) ?_
  rintro a ⟨x, -, rfl⟩
  by_cases hx : x ∈ Ω
  · exact le_csSup (bddAbove_deficit hC) ⟨x, hx, rfl⟩
  · beta_reduce
    rw [hoff x hx]
    exact deficitSup_nonneg hΩn hC hnn

/-- **Uniform convergence of the iteration of `dppOp`, on all of `ℝᵈ`.** -/
theorem dirIter_unif (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} (hΩm : MeasurableSet Ω)
    (hΩn : Ω.Nonempty) (hΩb : Bornology.IsBounded Ω)
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C)
    (hstep : ∀ x, u₀ x ≤ dppOp p ε Ω u₀ x) :
    ∀ η > 0, ∃ N, ∀ j ≥ N, ∀ x,
      |dirLimit p ε Ω u₀ x - dirIter p ε Ω u₀ j x| ≤ η := by
  set u := dirLimit p ε Ω u₀ with hu
  set w := dirIter p ε Ω u₀ with hw
  have hBMu : BddMeas u := bddMeas_dirLimit p ε hp hε hd hpd hΩm hu₀ hC hstep
  have hBM : ∀ j, BddMeas (w j) := fun j => bddMeas_dirIter p ε hp hε hpd hΩm hu₀ j
  have hle : ∀ j y, w j y ≤ u y := fun j y =>
    dirIter_le_dirLimit p ε hp hε hpd hΩm hu₀ hC j y
  have hnn : ∀ j y, 0 ≤ u y - w j y := fun j y => by linarith [hle j y]
  have hCd : ∀ j y, |u y - w j y| ≤ 2 * C := fun j y => by
    have h1 := abs_le.1 (abs_dirLimit_le p ε hp hε hpd hΩm hu₀ hC y)
    have h2 := abs_le.1 (abs_dirIter_le p ε hp hε hpd hΩm hu₀ hC j y)
    rw [abs_le]; constructor <;> linarith
  have hmono : ∀ j y, w j y ≤ w (j + 1) y := fun j y =>
    dirIter_mono p ε hp hε hd hpd hΩm hu₀ hstep j y
  have hconv : ∀ x, Tendsto (fun j => w j x) atTop (𝓝 (u x)) := fun x =>
    tendsto_dirIter p ε hp hε hd hpd hΩm hu₀ hC hstep x
  have hoff : ∀ j x, x ∉ Ω → u x - w j x = 0 := fun j x hx => by
    rw [hu, hw, dirLimit_eq_of_notMem p ε hx, dirIter_eq_of_notMem p ε hx]
    ring
  -- the set over which the deficit is measured
  set S := closureEps Ω ε
  have hS : S.Nonempty := closureEps_nonempty hΩn ε
  have hSfin : volume S ≠ ⊤ :=
    (isBounded_closureEps hΩn hΩb hε.le).measure_lt_top.ne
  obtain ⟨M, hlim⟩ := exists_deficitLimit hS hCd hnn hmono
  -- the three inputs of the estimate
  have hint : ∀ k, MeasureTheory.IntegrableOn (fun y => u y - w k y) S :=
    fun k => integrableOn_of_bddMeas (hBMu.sub (hBM k)) hSfin
  have hintlim : Tendsto (fun j => ∫ y in S, (u y - w j y)) atTop (𝓝 0) :=
    tendsto_setIntegral_deficit hSfin (fun j => (hBMu.sub (hBM j)).meas)
      hCd hconv
  have hglob : ∀ η > 0, ∀ δ' > 0, ∃ k, (∫ y in S, (u y - w k y)) ≤ η
      ∧ deficitSup S u (w k) ≤ M + δ' := fun η hη δ' hδ' =>
    exists_index_both hintlim hlim hη hδ'
  have hsel : ∀ (δ : ℝ), 0 < δ → ∀ k : ℕ, ∃ x₀ ∈ Ω, ∃ l : ℕ,
      M - 2 * δ ≤ tugOfWarOp p ε (w l) x₀ - tugOfWarOp p ε (w k) x₀ := by
    intro δ hδ k
    have hMk : ∀ k, M ≤ deficitSup Ω u (w (k + 1)) := fun k =>
      le_trans (le_deficitSup_of_antitone hS hCd hmono hlim (k + 1))
        (deficitSup_le_of_vanish hΩn hS (hCd (k + 1)) (hnn (k + 1))
          (hoff (k + 1)))
    obtain ⟨x₀, hx₀, l, hl⟩ := exists_sel hΩn hδ hMk hconv k
    refine ⟨x₀, hx₀, l, ?_⟩
    have e1 : w (l + 1) x₀ = tugOfWarOp p ε (w l) x₀ := by
      rw [hw, dirIter_succ, dppOp_of_mem p ε hx₀]
    have e2 : w (k + 1) x₀ = tugOfWarOp p ε (w k) x₀ := by
      rw [hw, dirIter_succ, dppOp_of_mem p ε hx₀]
    rw [e1, e2] at hl
    exact hl
  have hM : M ≤ 0 :=
    deficit_le_zero_gen p ε hp hε hpd (Ω := Ω) hBMu hBM hle hCd hnn hglob hint hsel
  have hzero := tendsto_deficitSup_zero hS hCd hnn hlim hM
  -- from the deficit suprema to a uniform bound
  intro η hη
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hzero.eventually (eventually_le_nhds hη))
  refine ⟨N, fun j hj x => ?_⟩
  rw [abs_of_nonneg (hnn j x)]
  by_cases hx : x ∈ S
  · exact le_trans (le_csSup (bddAbove_deficit (hCd j)) ⟨x, hx, rfl⟩) (hN j hj)
  · have hxΩ : x ∉ Ω := fun h => hx (subset_closureEps Ω ε h)
    rw [hoff j x hxΩ]
    exact hη.le

/-! ### The limit is a solution -/

/-- **The limit is a fixed point of the restricted operator.** -/
theorem dirLimit_fixed (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω)
    {u₀ : EuclSpace d → ℝ} (hu₀ : BddMeas u₀) {C : ℝ}
    (hC : ∀ y, |u₀ y| ≤ C)
    (hstep : ∀ x, u₀ x ≤ dppOp p ε Ω u₀ x) (x : EuclSpace d) :
    dppOp p ε Ω (dirLimit p ε Ω u₀) x = dirLimit p ε Ω u₀ x := by
  by_cases hx : x ∈ Ω
  swap
  · exact dppOp_of_notMem p ε hx _
  rw [dppOp_of_mem p ε hx]
  have hBMu := bddMeas_dirLimit p ε hp hε hd hpd hΩm hu₀ hC hstep
  have hunif := dirIter_unif p ε hp hε hd hpd hΩm ⟨x, hx⟩ hΩb hu₀ hC hstep
  set D := tugOfWarOp p ε (dirLimit p ε Ω u₀) x - dirLimit p ε Ω u₀ x
    with hD
  have key : ∀ η > 0, |D| ≤ 2 * η := by
    intro η hη
    obtain ⟨N, hN⟩ := hunif η hη
    have h1 : |tugOfWarOp p ε (dirLimit p ε Ω u₀) x
        - tugOfWarOp p ε (dirIter p ε Ω u₀ N) x| ≤ η :=
      tugOfWarOp_nonexpansive p ε hp hd hε hpd hBMu
        (bddMeas_dirIter p ε hp hε hpd hΩm hu₀ N)
        (fun y => hN N le_rfl y) x
    have h2 : |dirLimit p ε Ω u₀ x - dirIter p ε Ω u₀ (N + 1) x| ≤ η :=
      hN (N + 1) (Nat.le_succ N) x
    have h3 : dirIter p ε Ω u₀ (N + 1) x
        = tugOfWarOp p ε (dirIter p ε Ω u₀ N) x := by
      rw [dirIter_succ, dppOp_of_mem p ε hx]
    rw [h3] at h2
    have h4 := abs_le.1 h1
    have h5 := abs_le.1 h2
    rw [hD, abs_le]
    constructor <;> linarith
  have hDzero : D = 0 := by
    by_contra hcon
    have hpos : 0 < |D| := abs_pos.2 hcon
    have := key (|D| / 4) (by positivity)
    linarith
  linarith [hDzero, hD]

/-! ### Existence for the `ε`-problem with exterior data -/

open Classical in
/-- The starting function: `-C` on `Ω`, the data `F` outside. -/
def dirStart (Ω : Set (EuclSpace d)) (F : EuclSpace d → ℝ) (C : ℝ)
    (x : EuclSpace d) : ℝ :=
  if x ∈ Ω then -C else F x

lemma dirStart_of_mem {Ω : Set (EuclSpace d)} {F : EuclSpace d → ℝ} {C : ℝ}
    {x : EuclSpace d} (hx : x ∈ Ω) : dirStart Ω F C x = -C := by
  unfold dirStart; simp [hx]

lemma dirStart_of_notMem {Ω : Set (EuclSpace d)} {F : EuclSpace d → ℝ}
    {C : ℝ} {x : EuclSpace d} (hx : x ∉ Ω) : dirStart Ω F C x = F x := by
  unfold dirStart; simp [hx]

/-- **Existence for the `ε`-problem with exterior data.** For bounded measurable
data `F` with `|F| ≤ C`, there is a `p`-harmonious function in `Ω` with data `F`
that equals `F` outside `Ω` and is bounded by `C`. -/
theorem exists_pharmonious (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (hd : 0 < d)
    (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)} (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω)
    {F : EuclSpace d → ℝ} (hFm : Measurable F) {C : ℝ}
    (hFC : ∀ y, |F y| ≤ C) :
    ∃ u : EuclSpace d → ℝ, IsPHarmonious p ε Ω F u
      ∧ (∀ x, x ∉ Ω → u x = F x) ∧ ∀ y, |u y| ≤ C := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hFC 0)
  have hbd : ∀ y, |dirStart Ω F C y| ≤ C := by
    intro y
    by_cases hy : y ∈ Ω
    · rw [dirStart_of_mem hy, abs_neg, abs_of_nonneg hC0]
    · rw [dirStart_of_notMem hy]; exact hFC y
  have hmeas : Measurable (dirStart Ω F C) := by
    unfold dirStart
    exact Measurable.ite hΩm measurable_const hFm
  have hu₀ : BddMeas (dirStart Ω F C) := ⟨hmeas, ⟨C, hbd⟩⟩
  have hstep : ∀ x, dirStart Ω F C x ≤ dppOp p ε Ω (dirStart Ω F C) x := by
    intro x
    by_cases hx : x ∈ Ω
    · rw [dirStart_of_mem hx, dppOp_of_mem p ε hx]
      exact (abs_le.1 (abs_tugOfWarOp_le p ε hp hε hpd hu₀ hbd x)).1
    · exact (dppOp_of_notMem p ε hx _).symm.le
  refine ⟨dirLimit p ε Ω (dirStart Ω F C), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact bddMeas_dirLimit p ε hp hε hd hpd hΩm hu₀ hbd hstep
  · intro x hx
    have h := dirLimit_fixed p ε hp hε hd hpd hΩm hΩb hu₀ hbd hstep x
    rw [dppOp_of_mem p ε hx] at h
    exact h.symm
  · intro x hx
    rw [dirLimit_eq_of_notMem p ε hx.1, dirStart_of_notMem hx.1]
  · intro x hx
    rw [dirLimit_eq_of_notMem p ε hx, dirStart_of_notMem hx]
  · exact abs_dirLimit_le p ε hp hε hpd hΩm hu₀ hbd

/-! ### Existence and convergence together -/

/-- **Existence and convergence.** Let `Ω` be bounded and open with an exterior
sphere at every boundary point, and `F` bounded and continuous. Then for every
`ε > 0` the `ε`-problem has a `p`-harmonious solution with data `F`, equal to
`F` outside `Ω`, and these solutions converge uniformly on `closure Ω` to the
common value of the relaxed limits, which equals `F` on `frontier Ω`. -/
theorem pharmonious_exists_converge [Nontrivial (EuclSpace d)] (hd : 0 < d)
    {p : ℝ} (hp : 2 ≤ p) (hpd : 0 < p + (d : ℝ)) {Ω : Set (EuclSpace d)}
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) {F : EuclSpace d → ℝ}
    (hFc : Continuous F) {C : ℝ} (hFC : ∀ y, |F y| ≤ C)
    (hext : ∀ y ∈ frontier Ω, ∃ (z : EuclSpace d) (δ : ℝ), 0 < δ ∧
      ‖y - z‖ = δ ∧ ∀ x ∈ Ω, δ ≤ ‖x - z‖) :
    ∃ u : ℝ → EuclSpace d → ℝ,
      (∀ ε > 0, IsPHarmonious p ε Ω F (u ε)) ∧
      (∀ ε > 0, ∀ x, x ∉ Ω → u ε x = F x) ∧
      (∀ ε y, |u ε y| ≤ C) ∧
      (∀ x ∈ closure Ω, ubar u x = lbar u x) ∧
      (∀ x ∈ frontier Ω, ubar u x = F x) ∧
      (∀ η > 0, ∃ ε₀ > 0, ∀ ε, 0 < ε → ε < ε₀ → ∀ x ∈ closure Ω,
        |u ε x - ubar u x| ≤ η) := by
  have hex : ∀ ε : ℝ, 0 < ε → ∃ v : EuclSpace d → ℝ,
      IsPHarmonious p ε Ω F v ∧ (∀ x, x ∉ Ω → v x = F x) ∧ ∀ y, |v y| ≤ C :=
    fun ε hε => exists_pharmonious p ε hp hε hd hpd hΩo.measurableSet hΩb
      hFc.measurable hFC
  choose! U hU using hex
  set u : ℝ → EuclSpace d → ℝ := fun ε => if 0 < ε then U ε else F with hudef
  have hUeq : ∀ ε, 0 < ε → u ε = U ε := fun ε hε => by
    rw [hudef]; simp [hε]
  have hu : ∀ ε > 0, IsPHarmonious p ε Ω F (u ε) := fun ε hε => by
    rw [hUeq ε hε]; exact (hU ε hε).1
  have hout : ∀ ε > 0, ∀ x, x ∉ Ω → u ε x = F x := fun ε hε x hx => by
    rw [hUeq ε hε]; exact (hU ε hε).2.1 x hx
  have hC : ∀ ε y, |u ε y| ≤ C := fun ε y => by
    by_cases hε : 0 < ε
    · rw [hUeq ε hε]; exact (hU ε hε).2.2 y
    · have h : u ε = F := by rw [hudef]; simp [hε]
      rw [h]; exact hFC y
  obtain ⟨h1, h2, h3⟩ :=
    pharmonious_converge hd hp hpd hΩo hΩb hFc hext hC hu hout
  exact ⟨u, hu, hout, hC, h1, h2, h3⟩

end

end PLaplacian
