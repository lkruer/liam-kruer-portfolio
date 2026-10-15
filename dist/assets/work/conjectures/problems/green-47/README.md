# Green #47

**A counterexample to exact quadratic containment in Green’s Problem 47**

Jensen Kohlmeyer and Liam Kruer · September 8, 2026

[Read the proof](paper/proof.pdf) · [Lean source record](lean/) · [Submission notes](submission.md) · [All proofs](../../README.md#proof-index)

## Overview

| Field | Details |
| :--- | :--- |
| Collection | [Ben Green, *100 open problems*](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf), Problem 47 |
| Contribution | Counterexample to the exact-containment formulation (manuscript claim). |
| Manuscript | [PDF, 7 pages](paper/proof.pdf) |
| Manuscript date | September 8, 2026 |
| Manuscript review | Not independently reviewed in this repository |
| Lean | Uploaded; not checked |
| Submission | Draft; no announcement recorded |

## Problem and manuscript claim

The formulation considered asks whether occupying at most $(p+1)/2$ residue classes for sufficiently large primes forces either a counting bound of $O(\sqrt{X}/(\log X)^{100})$ or containment of every element in a rational quadratic image of the integers.

The manuscript proposes $A=\{2\}\cup\{q^2:q\text{ prime},\ q\equiv1\pmod8\}$ as a counterexample to that exact-containment implication.

## Scope and reading guide

Exact containment only. Both the PDF and the uploaded Lean header explicitly say this does not refute the formulation allowing finitely many exceptional elements, including Green and Harper’s Conjecture 1.7.

Theorem 1.1 states the three properties of the counterexample. Section 6 describes the exact target, source forms, and scope of the reported local checks.

## Formalization

`target : ¬ (fcTypeOfName% "Green47.green_47")`, observed in the uploaded source. The task wrapper supplies the enclosing `Bounty` namespace.

See the [Lean record](lean/README.md) for source availability, manuscript-reported checks, and materials needed to reproduce them. Repository compilation and mathematical review have not been performed.

## References and acknowledgments

The [original PDF](paper/proof.pdf) preserves the authors’ references and credits. The manuscript acknowledges assistance from OpenAI Codex in developing the construction, formalization, artifact checking, and manuscript preparation.

## Revision notes

- **2026-09-15:** Added the supplied manuscript and Lean submission body. Original file contents were preserved byte for byte. See [the manuscript record](paper/README.md), [SHA256SUMS](SHA256SUMS), and the [upload inventory](../../docs/upload-inventory.md).
