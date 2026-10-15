# Unit distances in convex polygons

[![Lean verification](https://github.com/lkruer/erdos-96-97-proof/actions/workflows/lean.yml/badge.svg)](https://github.com/lkruer/erdos-96-97-proof/actions/workflows/lean.yml)

**[Read the paper (PDF)](96-97.pdf)** · **[LaTeX source](96-97.tex)** · **[Lean proof](Erdos9697Complete.lean)**

**Authors:** Liam Kruer, Jensen Kohlmeyer, and Liam Price.

> **Repository history.** This repository republishes, unchanged, the history first published at `Leeham06972452/erdos-96-97`, which is no longer public. The version submitted for review is commit `0e98f5f9bdaf36007e3eb405cbefe2eda778a9b2`; the only later commit updates this README and `CITATION.cff` to the new address.

This repository contains the manuscript and a complete, single-file Lean 4 formalization of constructions giving negative answers to [Erdős problem 96](https://www.erdosproblems.com/96), [problem 97](https://www.erdosproblems.com/97), and the general conjecture that some universal bound on equal-distance multiplicity holds at a suitably chosen vertex of every convex polygon.

## Main result

Write $u(P)$ for the number of unordered unit-distance pairs in a finite planar set $P$, and $\delta_1(P)$ for the minimum number of unit-distance neighbours at any vertex.

For every sufficiently large integer $n$ and every $0<\eta<1/2$, there is an $n$-point set $P$ in strictly convex position such that

```math
\min\left\lbrace\delta_1(P),\frac{u(P)}{n}\right\rbrace
\ge \frac14\log_2\log_2 n-7\log_2\log_2\log_2 n.
```

The points can all lie in the union of the two open disks of radius $\eta$ centred at $(0,-1/2)$ and $(0,1/2)$. The threshold for $n$ is independent of $\eta$. The full unit-distance graph is bipartite, with its classes separated by the horizontal axis.

Consequently:

- **Problem 96:** the maximum number of unit distances among vertices of a convex $n$-gon is $\Omega(n\log\log n)$, so it is not $O(n)$.
- **Problem 97:** a strictly convex polygon exists in which every vertex has at least four other vertices at distance exactly one.
- **General fixed-k conjecture:** for every integer $k\ge1$ and every sufficiently large $n$, there is such a polygon with at least $k$ unit-distance neighbours at every vertex.

The manuscript also gives the explicit upper bound $3432\cdot2^{36036}$ on the number of vertices needed for a counterexample to problem 97. This is a cardinality bound; the construction uses an existence argument for the coordinates.

## Verify the Lean proof

Install [Lean through elan](https://github.com/leanprover/elan), then run:

```sh
git clone https://github.com/lkruer/erdos-96-97-proof.git
cd erdos-96-97-proof
lake exe cache get
lake build
```

The first run downloads the pinned toolchain and Mathlib dependencies. The cache command retrieves Mathlib's compiled library files. The default build target is `Erdos9697Complete`.

To run the proof file directly and display its axiom-audit messages, use:

```sh
lake env lean Erdos9697Complete.lean
```

The build environment is pinned to:

| Component | Version |
| --- | --- |
| Lean | `leanprover/lean4:v4.33.1` |
| Mathlib | [`0df444a360eaa60ab8c11dca51a86af692955474`](https://github.com/leanprover-community/mathlib4/commit/0df444a360eaa60ab8c11dca51a86af692955474), the `v4.33.1` release |
| Transitive dependencies | Exact revisions in `lake-manifest.json` |

The supplied proof was checked locally on 13 September 2026 with this Lean/Mathlib combination. Its final section audits the transitive axiom dependencies of 33 results and fails if any depends on an axiom outside `propext`, `Classical.choice`, and `Quot.sound`. This includes rejecting `sorryAx`. The only import is `Mathlib`; the problem definitions are reproduced in the file without importing unproved conjectures.

The [GitHub Actions workflow](.github/workflows/lean.yml) builds the proof on pushes and pull requests. The badge above reports the current workflow status.

## Main Lean entry points

All the following declarations are in the `Proof` namespace in [Erdos9697Complete.lean](Erdos9697Complete.lean).

| Declaration | Statement |
| --- | --- |
| `main_theorem` | The constant-quantified main theorem of the manuscript |
| `main_quantitative` | The main theorem with the explicit constant $C=7$ |
| `finite_construction_plane` | The finite middle-levels construction in the Euclidean plane |
| `threshold_configuration_plane` | Minimum degree and edge density at every cardinality beyond a threshold |
| `convex_unit_distances_omega` | The $\Omega(n\log\log n)$ lower bound |
| `eventual_minimum_degree` | Arbitrarily large fixed minimum degree for all sufficiently large cardinalities |
| `explicit_erdos_97_counterexample` | The counterexample with at most $3432\cdot2^{36036}$ vertices |
| `erdos_96_false` | Negation of the linear upper-bound conjecture |
| `erdos_97_false` | Negation of the four-equidistant-vertices conjecture |
| `erdos_97_general_false` | Negation of the general fixed-k conjecture |

## Build the PDF

The checked-in [PDF](96-97.pdf) is compiled from [96-97.tex](96-97.tex). With a LaTeX distribution and `latexmk` installed:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error 96-97.tex
```

Alternatively, [Tectonic](https://tectonic-typesetting.github.io/) downloads the required TeX resources and handles the reference-resolution passes:

```sh
tectonic 96-97.tex
```

The PDF included in the initial upload was built with Tectonic 0.17.0. Generated LaTeX auxiliary files and local Lean build products are excluded by `.gitignore`.

## Citation

Citation metadata is provided in [CITATION.cff](CITATION.cff). A BibTeX entry for the manuscript is:

```bibtex
@unpublished{kruer2026unitdistances,
  author = {Kruer, Liam and Kohlmeyer, Jensen and Price, Liam},
  title = {Unit distances in convex polygons},
  year = {2026},
  note = {Manuscript with a Lean 4 formalization},
  url = {https://github.com/lkruer/erdos-96-97-proof}
}
```

## Provenance and references

The manuscript includes an AI disclosure describing the role of GPT 6 Astra in the construction, subsequent development, and exposition. The authors retain responsibility for the work. The full disclosure and mathematical references are in the [paper](96-97.pdf).

The compatibility definitions at the start of the Lean file retain the attribution and Apache 2.0 license reference of their Formal Conjectures sources. The problem statements can also be compared with the [Formal Conjectures entry for 96](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/96.lean) and [entry for 97](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/97.lean).

Corrections and mathematical questions can be raised through the repository's [issues](https://github.com/lkruer/erdos-96-97-proof/issues).
