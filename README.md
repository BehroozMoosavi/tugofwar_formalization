# Formalized convergence for the tug-of-war scheme of the normalized p-Laplacian

A Lean 4 formalization of the convergence theory of the dynamic programming
scheme (tug-of-war with noise) for the normalized p-Laplacian, for $2 \le p < \infty$.

The main theorem states that $p$-harmonious functions — the solutions of the
discrete dynamic programming principle — converge uniformly to the viscosity
solution of the limit equation

$$
-\Delta_p^N u = 0, \qquad \Delta_p^N u = \Delta u + (p-2)\left\langle D^2 u\,\frac{\nabla u}{|\nabla u|}, \frac{\nabla u}{|\nabla u|}\right\rangle .
$$

The development follows the analytic route throughout: no games, strategies,
stopping times or martingales appear. The dynamic programming principle is
the definition of the discrete problem.

## Status

- **Complete:** every theorem is fully proved. The library contains no `sorry`.
- **Axioms:** the main theorem depends only on Lean's standard axioms,
  `propext`, `Classical.choice` and `Quot.sound`.
- **Size:** 28,502 lines in 222 files.

## The main theorem

`PLaplacian.pharmonious_converge`, in `Plaplacian/MainConv.lean`:

> Let $2 \le p$ and $d \ge 1$, let $\Omega \subseteq \mathbb{R}^d$ be bounded and
> open with an exterior sphere at every boundary point, and let $F$ be continuous.
> Let $(u_\varepsilon)_{\varepsilon > 0}$ be uniformly bounded, each $u_\varepsilon$
> $p$-harmonious in $\Omega$ with data $F$ and equal to $F$ outside $\Omega$.
> Then the upper and lower half-relaxed limits coincide on $\overline\Omega$,
> equal $F$ on $\partial\Omega$, and $u_\varepsilon \to \overline u$ uniformly on
> $\overline\Omega$.

This completes the Barles–Souganidis argument for the scheme. The theorem takes
the family $(u_\varepsilon)$ as given; it is a convergence theorem, not an
existence theorem for the $\varepsilon$-problem with exterior data.

## What is formalized

**Layer 1 — the discrete theory.** The step operator $T_\varepsilon$, with
monotonicity, translation equivariance and nonexpansiveness; Borel
measurability of the extreme values over open balls; existence by Perron
iteration with uniform convergence; and the discrete comparison principle,
following Luiro–Parviainen–Saksman.

**Layer 2 — the viscosity framework.** The operator in generator form with
degenerate ellipticity; sub- and supersolution predicates, with the singular
set $\{\nabla u = 0\}$ treated through semicontinuous envelopes; the
second-order necessary condition; consistency with classical solutions; and
stability.

**Layer 3 — the asymptotic expansion.**

$$
T_\varepsilon\varphi(x) = \varphi(x) + \frac{\varepsilon^2}{2(p+d)}\,\Delta_p^N\varphi(x) + o(\varepsilon^2),
$$

for test functions with nonvanishing gradient, with both halves (the average
and the extreme values), the singular case, and the error at an explicit rate.

**Layer 4 — convergence.**
- The half-relaxed limits are viscosity sub- and supersolutions.
- **Alexandrov's theorem**, through the proximal map, with neither the
  Hahn–Banach theorem nor integration.
- **Jensen's lemma**, with neither mollification nor the area formula.
- The strong maximum and minimum principles.
- **The comparison principle** for the homogeneous equation: a change of
  values makes the supersolution strict away from critical points, and spatial
  translations handle the critical points.
- **Boundary behaviour** under an exterior sphere condition, through a
  polynomial barrier and a discrete comparison principle.
- **Uniform convergence** on $\overline\Omega$.

Results of independent interest, absent from Mathlib, include Alexandrov's
theorem, Jensen's lemma, monotonicity of the set average
(`setAverage_mono`), the second-order necessary condition at an interior
extremum, and the second-moment tensor of a Euclidean ball.

## Key files

| File | Contents |
|---|---|
| `StepOperator.lean`, `Domain.lean` | the operator $T_\varepsilon$ and the $\varepsilon$-Dirichlet problem |
| `Existence.lean`, `ComparisonFinal.lean` | existence and comparison for the discrete problem |
| `Operator.lean`, `Viscosity.lean` | the limit operator and the viscosity predicates |
| `Expansion.lean` | the asymptotic expansion of $T_\varepsilon$ |
| `ViscC2.lean` | the relaxed limits are viscosity sub- and supersolutions |
| `Alexandrov.lean`, `JensenProduct.lean` | Alexandrov's theorem and Jensen's lemma |
| `SMP.lean`, `CompFull.lean` | the strong maximum principle and the comparison principle |
| `BdryEst.lean` | the boundary estimate |
| `MainConv.lean` | **the main theorem** |

## Building

Requirements: [elan](https://github.com/leanprover/elan), the Lean version
manager. The toolchain is pinned in `lean-toolchain`
(`leanprover/lean4:v4.34.0-rc2`) and Mathlib in `lake-manifest.json`
(commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`).

```bash
git clone https://github.com/BehroozMoosavi/tugofwar_formalization.git
cd tugofwar_formalization
lake exe cache get   # download precompiled Mathlib (much faster than building it)
lake build
```

## Checking the result

To confirm that the main theorem rests only on the standard axioms, create a
file `Check.lean` containing

```lean
import Plaplacian
#print axioms PLaplacian.pharmonious_converge
```

and run `lake env lean Check.lean`. The expected output is

```
'PLaplacian.pharmonious_converge' depends on axioms: [propext, Classical.choice, Quot.sound]
```

To confirm there is no `sorry`, run `grep -rn "sorry" Plaplacian/`; it prints nothing.

## Paper

J. J. Manfredi and B. Moosavi, *A formalized convergence theory for the dynamic
programming scheme of the normalized p-Laplacian*, in preparation. The paper
describes the architecture, the mathematical arguments, and fifty findings in
which formalization corrected or constrained the intended development.

## How the development was produced

The formalization was carried out with extensive use of a large language
model (Anthropic's Claude), which drafted Lean files under the authors'
direction. Every file was compiled against the pinned toolchain, and the
result is checked by Lean's kernel; no trust in the model is required to
trust the theorems.

## Authors

- Juan J. Manfredi, University of Pittsburgh — manfredi@pitt.edu
- Behrooz Moosavi, University of Pittsburgh — behroozmoosavi@pitt.edu

## License

Apache 2.0. See [LICENSE](LICENSE).
