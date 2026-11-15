/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
module

public import Mathlib
public import Plaplacian.AsmCond

@[expose] public section

/-!
# The limit argument with a frequent bound

A gap in the chain, found late and worth recording. The contact points arrive
frequently along the filter, not eventually: a solution is bounded and Borel
but not continuous, so the difference need not attain its maximum, and only
near-maximizers are available. The limit argument as first proved takes an
eventual bound, and frequently is strictly weaker, so the chain did not
connect.

It connects with a frequent bound. If the quotient tends to zero and lies
below the operator value frequently, then that value is nonnegative: were it
negative, the quotient would eventually exceed it, contradicting the
frequency.

An informal treatment closes this gap by passing to a subsequence and does not
usually dwell on it. What it shows is that the discrete solution's lack of
regularity propagates all the way to the quantifier on the filter in the limit
argument.

## Main results

- nonneg_of_frequently
- nonpos_of_frequently
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # The limit argument with a frequent bound

A gap we had not noticed: the contact points come *frequently* along the
filter, not eventually, because they are near-maximizers of a function that
need not attain its maximum. But the limit argument as proved takes an
eventual bound.

Frequently is weaker than eventually, so the chain as it stood does not
connect. It does connect with a frequent bound, and the argument is short: if
the limit of `q` is zero and `q ε ≤ I` frequently, then `0 ≤ I`, for
otherwise `I < 0` and `q` tends to zero, so `q ε > I` eventually, which
contradicts the frequency.

This is the kind of gap that a careful informal proof also has to address and
usually does so silently, by remarking that one may pass to a subsequence.
-/


/-- **The limit argument with a frequent bound.** -/
theorem nonneg_of_frequently {I : ℝ} {q : ℝ → ℝ}
    (hq : Filter.Tendsto q (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hfreq : ∃ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), q ε ≤ I) :
    0 ≤ I := by
  by_contra hcon
  push Not at hcon
  -- q is eventually above I, since it tends to zero and I < 0
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), I < q ε := by
    have h := hq.eventually (eventually_gt_nhds hcon)
    exact h
  -- that contradicts the frequency
  have hboth := hfreq.and_eventually hev
  rw [Filter.frequently_iff] at hboth
  obtain ⟨ε, _, hle, hlt⟩ := hboth Filter.univ_mem
  linarith [hle, hlt]

/-- And the dual. -/
theorem nonpos_of_frequently {I : ℝ} {q : ℝ → ℝ}
    (hq : Filter.Tendsto q (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hfreq : ∃ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), I ≤ q ε) :
    I ≤ 0 := by
  by_contra hcon
  push Not at hcon
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), q ε < I := by
    exact hq.eventually (eventually_lt_nhds hcon)
  have hboth := hfreq.and_eventually hev
  rw [Filter.frequently_iff] at hboth
  obtain ⟨ε, _, hge, hlt⟩ := hboth Filter.univ_mem
  linarith [hge, hlt]

end

end PLaplacian
