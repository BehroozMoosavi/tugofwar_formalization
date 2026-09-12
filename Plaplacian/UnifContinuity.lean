import Plaplacian.Selection

open MeasureTheory Metric Set Filter

namespace PLaplacian

noncomputable section

variable {d : ℕ}

theorem abs_sSup_sub_sSup_le {S : Set (EuclSpace d)} (hS : S.Nonempty)
    {u v : EuclSpace d → ℝ} {K : ℝ} (hK : ∀ y, |u y - v y| ≤ K)
    {C : ℝ} (hCu : ∀ y, |u y| ≤ C) (hCv : ∀ y, |v y| ≤ C) :
    |sSup (u '' S) - sSup (v '' S)| ≤ K := by
  have hbu : BddAbove (u '' S) :=
    ⟨C, by rintro a ⟨y, -, rfl⟩; exact (abs_le.1 (hCu y)).2⟩
  have hbv : BddAbove (v '' S) :=
    ⟨C, by rintro a ⟨y, -, rfl⟩; exact (abs_le.1 (hCv y)).2⟩
  have h1 : sSup (u '' S) ≤ sSup (v '' S) + K := by
    refine csSup_le (hS.image u) ?_
    rintro a ⟨y, hy, rfl⟩
    have h2 : u y ≤ v y + K := by linarith [(abs_le.1 (hK y)).2]
    have h3 : v y ≤ sSup (v '' S) := le_csSup hbv ⟨y, hy, rfl⟩
    linarith
  have h4 : sSup (v '' S) ≤ sSup (u '' S) + K := by
    refine csSup_le (hS.image v) ?_
    rintro a ⟨y, hy, rfl⟩
    have h2 : v y ≤ u y + K := by linarith [(abs_le.1 (hK y)).1]
    have h3 : u y ≤ sSup (u '' S) := le_csSup hbu ⟨y, hy, rfl⟩
    linarith
  rw [abs_le]
  constructor <;> linarith

theorem abs_sInf_sub_sInf_le {S : Set (EuclSpace d)} (hS : S.Nonempty)
    {u v : EuclSpace d → ℝ} {K : ℝ} (hK : ∀ y, |u y - v y| ≤ K)
    {C : ℝ} (hCu : ∀ y, |u y| ≤ C) (hCv : ∀ y, |v y| ≤ C) :
    |sInf (u '' S) - sInf (v '' S)| ≤ K := by
  have hbu : BddBelow (u '' S) :=
    ⟨-C, by rintro a ⟨y, -, rfl⟩; exact (abs_le.1 (hCu y)).1⟩
  have hbv : BddBelow (v '' S) :=
    ⟨-C, by rintro a ⟨y, -, rfl⟩; exact (abs_le.1 (hCv y)).1⟩
  have h1 : sInf (u '' S) ≤ sInf (v '' S) + K := by
    have hstep : sInf (u '' S) - K ≤ sInf (v '' S) := by
      refine le_csInf (hS.image v) ?_
      rintro a ⟨y, hy, rfl⟩
      have h2 : u y - K ≤ v y := by linarith [(abs_le.1 (hK y)).2]
      have h3 : sInf (u '' S) ≤ u y := csInf_le hbu ⟨y, hy, rfl⟩
      linarith
    linarith
  have h4 : sInf (v '' S) ≤ sInf (u '' S) + K := by
    have hstep : sInf (v '' S) - K ≤ sInf (u '' S) := by
      refine le_csInf (hS.image u) ?_
      rintro a ⟨y, hy, rfl⟩
      have h2 : v y - K ≤ u y := by linarith [(abs_le.1 (hK y)).1]
      have h3 : sInf (v '' S) ≤ v y := csInf_le hbv ⟨y, hy, rfl⟩
      linarith
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- The average term is also uniformly continuous. -/
theorem abs_setAverage_sub_le {u v : EuclSpace d → ℝ}
    (hu : BddMeas u) (hv : BddMeas v) {K : ℝ} (hK : ∀ y, |u y - v y| ≤ K)
    (x : EuclSpace d) {ε : ℝ} (hε : 0 < ε) :
    |(⨍ y in ball x ε, u y) - ⨍ y in ball x ε, v y| ≤ K := by
  have h1 : (⨍ y in ball x ε, u y) ≤ (⨍ y in ball x ε, v y) + K := by
    have hc : (⨍ _y in ball x ε, K) = K := setAverage_const_ball K x hε
    have hstep : (⨍ y in ball x ε, u y)
        ≤ ⨍ y in ball x ε, (v y + K) := by
      refine setAverage_mono_ball x (hu.integrableOn_ball x ε) ?_ ?_
      · exact (hv.add_const' K).integrableOn_ball x ε
      · exact fun y => by linarith [(abs_le.1 (hK y)).2]
    have heq : (⨍ y in ball x ε, (v y + K))
        = (⨍ y in ball x ε, v y) + K := by
      rw [show (fun y : EuclSpace d => v y + K) = v + (fun _ => K) from rfl,
          MeasureTheory.setAverage_add (hv.integrableOn_ball x ε)
            integrableOn_const, hc]
    linarith [hstep, heq]
  have h4 : (⨍ y in ball x ε, v y) ≤ (⨍ y in ball x ε, u y) + K := by
    have hc : (⨍ _y in ball x ε, K) = K := setAverage_const_ball K x hε
    have hstep : (⨍ y in ball x ε, v y)
        ≤ ⨍ y in ball x ε, (u y + K) := by
      refine setAverage_mono_ball x (hv.integrableOn_ball x ε) ?_ ?_
      · exact (hu.add_const' K).integrableOn_ball x ε
      · exact fun y => by linarith [(abs_le.1 (hK y)).1]
    have heq : (⨍ y in ball x ε, (u y + K))
        = (⨍ y in ball x ε, u y) + K := by
      rw [show (fun y : EuclSpace d => u y + K) = u + (fun _ => K) from rfl,
          MeasureTheory.setAverage_add (hu.integrableOn_ball x ε)
            integrableOn_const, hc]
    linarith [hstep, heq]
  rw [abs_le]
  constructor <;> linarith

end

end PLaplacian
