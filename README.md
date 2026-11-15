# A formally verified convergence theory for the tug-of-war scheme of the normalized p-Laplacian

A Lean 4 formalization of the dynamic programming scheme (tug-of-war with noise)
for the normalized p-Laplacian, $2 \le p < \infty$: **existence, uniqueness and
convergence**, at the level of the discrete problem and of the limit equation.

The limit equation is

$$
-\Delta_p^N u = 0, \qquad \Delta_p^N u = \Delta u + (p-2)\left\langle D^2 u\,\frac{\nabla u}{|\nabla u|}, \frac{\nabla u}{|\nabla u|}\right\rangle ,
$$

and the discrete problem is the dynamic programming principle

$$
u_\varepsilon(x) = \frac{\alpha}{2}\Big(\sup_{B_\varepsilon(x)} u_\varepsilon + \inf_{B_\varepsilon(x)} u_\varepsilon\Big) + \beta \fint_{B_\varepsilon(x)} u_\varepsilon,
\qquad \alpha = \frac{p-2}{p+d}, \quad \beta = \frac{d+2}{p+d}.
$$

Its solutions are called $p$-harmonious functions. The development follows the
analytic route throughout: no games, strategies, stopping times or martingales
appear.

## Status

- **Complete:** every theorem is fully proved; the library contains no `sorry`.
- **Axioms:** the main theorems depend only on Lean's standard axioms,
  `propext`, `Classical.choice` and `Quot.sound`.
- **Size:** 225 Lean files in `Plaplacian/` (29,380 lines at `v1.3`).
- **Versions of this commit:** Lean `4.35.0` (toolchain `leanprover/lean4:v4.35.0`),
  Mathlib `v4.35.0` (commit `56a005855ea17e0b0958f73ec801ae140b0a1679`). The library uses the Lean module
  system, and `Challenge.lean`, `Solution.lean`, `comparator.json` and
  `formalization.yaml` are the files for the Palomar registry.
- **Release described in the papers:** tag [`v1.3`](../../tree/v1.3), built
  with Lean `4.34.0-rc2` (toolchain `leanprover/lean4:v4.34.0-rc2`) and
  Mathlib commit `85e3a25e006c35636f0e53b0e9296caca2685bc0`. The theorem
  statements are the same in both versions.

## Main results

| Theorem | Statement |
|---|---|
| `PLaplacian.pharmonious_exists_converge` | **Existence and convergence** (the main theorem) |
| `PLaplacian.pharmonious_converge` | convergence for every admissible family |
| `PLaplacian.exists_pharmonious` | existence for the discrete problem |
| `PLaplacian.pharmonious_unique` | **uniqueness for the discrete problem** |
| `PLaplacian.visc_comparison` | the comparison principle for the limit equation |
| `PLaplacian.visc_unique` | **uniqueness of viscosity solutions** |

**The main theorem.** Let $2 \le p < \infty$ and $d \ge 1$, let
$\Omega \subset \mathbb{R}^d$ be a bounded open set satisfying the exterior
sphere condition, and let $F$ be bounded and continuous. Then:

1. for every $\varepsilon > 0$ there is a unique $p$-harmonious function
   $u_\varepsilon$ in $\Omega$ with data $F$ that equals $F$ outside $\Omega$;
2. as $\varepsilon \to 0$, $u_\varepsilon$ converges uniformly on
   $\overline\Omega$ to the unique viscosity solution of $-\Delta_p^N u = 0$
   in $\Omega$ with boundary values $F$.

This completes the Barles–Souganidis argument for the scheme.

## What is formalized

**Layer 1: the discrete theory.** The step operator $T_\varepsilon$, with
monotonicity, translation equivariance and nonexpansiveness; Borel
measurability of the extreme values over open balls; the discrete comparison
principle; existence by iteration of the operator restricted to the domain,
with uniform convergence by the estimate of Luiro, Parviainen and Saksman; and
uniqueness, by propagating near-maxima of the difference of two solutions
across the domain, following the strategy of Luiro, Parviainen and Saksman
(Theorem 2.2 of their paper).

**Layer 2: the viscosity framework.** The operator with degenerate ellipticity;
sub- and supersolutions, with the singular set $\{\nabla u = 0\}$ treated
through semicontinuous envelopes; the second-order necessary condition;
consistency with classical solutions; and stability.

**Layer 3: the asymptotic expansion.**

$$
T_\varepsilon\varphi(x) = \varphi(x) + \frac{\varepsilon^2}{2(p+d)}\,\Delta_p^N\varphi(x) + o(\varepsilon^2)
$$

for test functions with nonvanishing gradient, with both halves (the average
and the extreme values), the singular case, and an explicit error rate.

**Layer 4: convergence and the limit equation.**
- The half-relaxed limits are viscosity sub- and supersolutions.
- **Aleksandrov's theorem**, through the proximal map, with neither the
  Hahn–Banach theorem nor integration.
- **Jensen's lemma**, with neither mollification nor the area formula.
- The strong maximum and minimum principles.
- **The comparison principle** for the homogeneous equation: a change of values
  makes the supersolution strict away from critical points, and spatial
  translations handle the critical points. Uniqueness of viscosity solutions
  follows.
- **Boundary behaviour** under an exterior sphere condition, through a
  polynomial barrier and a discrete comparison principle.
- **Uniform convergence** on $\overline\Omega$.

Results absent from Mathlib include Aleksandrov's theorem, Jensen's lemma,
monotonicity of the set average (`setAverage_mono`), the second-order necessary
condition at an interior extremum, and the second moments of a Euclidean ball.

## Key files

| File | Contents |
|---|---|
| `StepOperator.lean`, `Domain.lean` | the operator $T_\varepsilon$ and the $\varepsilon$-problem |
| `DirichletExistence.lean` | existence, and the unconditional main theorem |
| `DiscUnique.lean` | uniqueness for the discrete problem |
| `Operator.lean`, `Viscosity.lean` | the limit operator and the viscosity predicates |
| `Expansion.lean` | the asymptotic expansion of $T_\varepsilon$ |
| `ViscC2.lean` | the relaxed limits are viscosity sub- and supersolutions |
| `Alexandrov.lean`, `JensenProduct.lean` | Aleksandrov's theorem and Jensen's lemma |
| `SMP.lean`, `CompFull.lean` | the strong maximum principle and the comparison principle |
| `ViscUnique.lean` | uniqueness of viscosity solutions |
| `BdryEst.lean` | the boundary estimate |
| `MainConv.lean` | convergence |

## Documentation

The [`docs/`](docs/) folder contains, each as a PDF with its LaTeX source:

- **the article**, *A formally verified convergence theorem for the tug-of-war
  scheme of the normalized p-Laplacian* ([`docs/article/`](docs/article/));
- **the technical companion**, which documents every layer of the development
  and fifty-one findings in which formalization corrected or constrained the
  informal argument ([`docs/technical-companion.pdf`](docs/technical-companion.pdf));
- **the blueprint**: every definition and theorem with the Lean declarations
  that prove it and a dependency graph ([`docs/blueprint/`](docs/blueprint/)).

The blueprint can also be built as a website on which each statement shows the
exact Lean code that proves it:

```bash
python3 docs/blueprint/site/build.py
open _site/index.html
```

## Building

Requirements: [elan](https://github.com/leanprover/elan), the Lean version
manager. The toolchain is pinned in `lean-toolchain` and Mathlib in
`lake-manifest.json`.

```bash
git clone https://github.com/BehroozMoosavi/tugofwar_formalization.git
cd tugofwar_formalization
lake exe cache get   # download precompiled Mathlib (much faster than building it)
lake build
```

## Checking the results

To confirm that the main theorems rest only on the standard axioms, create a
file `Check.lean` containing

```lean
import Plaplacian
#print axioms PLaplacian.pharmonious_exists_converge
#print axioms PLaplacian.pharmonious_unique
#print axioms PLaplacian.visc_unique
```

and run `lake env lean Check.lean`. Each line of the output ends with

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

To confirm there is no `sorry`, run `grep -rn "sorry" Plaplacian/`; it prints
nothing.

## Releases

| Tag | Contents |
|---|---|
| `v1.0` | convergence, assuming the family of solutions exists |
| `v1.1` | existence for the discrete problem; unconditional convergence |
| `v1.2` | uniqueness of viscosity solutions |
| `v1.3` | uniqueness for the discrete problem; the version described in the papers |

## Paper

J. J. Manfredi and B. Moosavi, *A formally verified convergence theorem for the
tug-of-war scheme of the normalized p-Laplacian*, submitted to arXiv, 2026.

## How the development was produced

The formalization was carried out with extensive use of a large language model
(Anthropic's Claude), which drafted Lean files under the authors' direction.
The mathematical route was fixed by the authors. Every file was compiled
against the pinned toolchain, and the result is checked by Lean's kernel; no
trust in the model is needed to trust the theorems.

## Authors

- Juan J. Manfredi, University of Pittsburgh: manfredi@pitt.edu
- Behrooz Moosavi, University of Pittsburgh: behroozmoosavi@pitt.edu

## License

Apache 2.0. See [LICENSE](LICENSE).
