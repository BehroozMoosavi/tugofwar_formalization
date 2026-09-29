/-
Copyright (c) 2026 Behrooz Moosavi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Behrooz Moosavi
-/
import Mathlib
import Plaplacian.LowerSemi

/-!
# Towards the sequence extraction

The extraction of contact points needs sequences of parameters tending to zero
and points tending to the base point, along the relaxed filter. That filter is
a product of the punctured right neighbourhood of zero in the reals with a
neighbourhood in a metric space, both first countable, so the product is
countably generated and admits such a sequence.

The countable generation is registered as an instance. Instance resolution does
not see through a definition, so without it every use would have to unfold the
filter by hand.

## Main results

- relaxFilter_countablyGenerated
- exists_seq_relax
-/

open Set Topology Filter MeasureTheory Metric

namespace PLaplacian

noncomputable section

variable {d : ℕ}

/-! # Towards the sequence extraction

The extraction needs sequences `εₙ → 0` and `yₙ → x` along which the family
approaches `ubar u x`. That is the sequential characterisation of the limit
superior, available when the filter is countably generated.

`relaxFilter x` is a product of the punctured right neighbourhood of zero in
the reals with a neighbourhood in a metric space. Both are first countable,
hence countably generated, and a product of two such is countably generated.

This probe establishes that, and looks for the sequential characterisation.
-/


/-- The relaxed filter is countably generated. Registered as an instance so
that downstream uses do not have to unfold the definition: instance
resolution does not see through a def, and every use would otherwise repeat
the unfolding. -/
instance relaxFilter_countablyGenerated (x : EuclSpace d) :
    (relaxFilter x).IsCountablyGenerated := by
  unfold relaxFilter
  infer_instance

/-- Hence there is a sequence tending along it. -/
theorem exists_seq_relax (x : EuclSpace d) :
    ∃ q : ℕ → ℝ × EuclSpace d,
      Filter.Tendsto q Filter.atTop (relaxFilter x) := by
  exact Filter.exists_seq_tendsto (relaxFilter x)

/-! The sequence gives `εₙ = (q n).1 → 0⁺` and `yₙ = (q n).2 → x`, which is
the extraction's raw material. What remains is to choose the sequence so that
the values approach the limit superior, which is where the `limsup`'s
definition as an infimum of suprema is unpacked. -/


end

end PLaplacian
