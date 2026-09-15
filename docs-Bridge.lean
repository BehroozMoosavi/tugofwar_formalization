import Mathlib

open Set Topology Filter

/-!
# The iteratedDerivWithin bridge

`taylor_mean_remainder_lagrange` states everything with
`iteratedDerivWithin n f (uIcc a b)`; the line machinery produces plain
`deriv`. The bridge rests on `derivWithin_of_mem_nhds`: if the set is a
neighbourhood of the point then `derivWithin` is `deriv`, and `uIcc a b` is a
neighbourhood of every interior point, so no `UniqueDiffOn` argument is
needed.

At order two there is one subtlety. After unfolding, the goal involves
`derivWithin (derivWithin g (uIcc a b)) (uIcc a b) t`, and the inner
`derivWithin g (uIcc a b)` must be shown to agree with `deriv g` on a whole
neighbourhood of `t`, not merely at `t`, before it can be differentiated
again. That is `Filter.EventuallyEq.deriv_eq`, and the neighbourhood is the
open interval `Ioo (min a b) (max a b)`.
-/

/-- The interval is a neighbourhood of any interior point. -/
theorem uIcc_mem_nhds {a b t : ℝ} (ht : t ∈ Ioo (min a b) (max a b)) :
    uIcc a b ∈ nhds t := by
  rw [uIcc]
  exact Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Icc_self

/-- Order one. -/
theorem iteratedDerivWithin_one_eq (g : ℝ → ℝ) {a b t : ℝ}
    (ht : t ∈ Ioo (min a b) (max a b)) :
    iteratedDerivWithin 1 g (uIcc a b) t = deriv g t := by
  rw [iteratedDerivWithin_one]
  exact derivWithin_of_mem_nhds (uIcc_mem_nhds ht)

/-- The inner derivative agrees with `deriv g` on a neighbourhood of `t`,
because every point of the open interval has the interval as a
neighbourhood. -/
theorem derivWithin_eventuallyEq (g : ℝ → ℝ) {a b t : ℝ}
    (ht : t ∈ Ioo (min a b) (max a b)) :
    derivWithin g (uIcc a b) =ᶠ[nhds t] deriv g := by
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact derivWithin_of_mem_nhds (uIcc_mem_nhds hs)

/-- **Order two.** -/
theorem iteratedDerivWithin_two_eq (g : ℝ → ℝ) {a b t : ℝ}
    (ht : t ∈ Ioo (min a b) (max a b)) :
    iteratedDerivWithin 2 g (uIcc a b) t = deriv (deriv g) t := by
  rw [show (2 : Nat) = 1 + 1 from rfl, iteratedDerivWithin_succ,
      iteratedDerivWithin_one]
  rw [derivWithin_of_mem_nhds (uIcc_mem_nhds ht)]
  exact (derivWithin_eventuallyEq g ht).deriv_eq

#check @Filter.EventuallyEq.deriv_eq
