# Green #15

**A Lipschitz integer graph without three-term arithmetic progressions**

Jensen Kohlmeyer and Liam Kruer · September 10, 2026

[Read the proof](paper/proof.pdf) · [Lean source record](lean/) · [Submission notes](submission.md) · [All proofs](../../README.md#proof-index)

## Overview

| Field | Details |
| :--- | :--- |
| Collection | [Ben Green, *100 open problems*](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf), Problem 15 |
| Contribution | Affirmative construction (manuscript claim). |
| Manuscript | [PDF, 8 pages](paper/proof.pdf) |
| Manuscript date | September 10, 2026 |
| Manuscript review | Not independently reviewed in this repository |
| Lean | Uploaded; not checked |
| Submission | Draft; no announcement recorded |

## Problem and manuscript claim

Green’s Problem 15 asks for a Lipschitz function $F:\mathbb{N}\to\mathbb{Z}$ whose graph contains no nontrivial three-term arithmetic progression.

The manuscript claims a strictly increasing, 125-Lipschitz function whose successive differences belong to a specified set of sixteen positive integers and whose graph is progression-free.

## Scope and reading guide

The claimed construction concerns the full existence question for a Lipschitz graph. The manuscript does not assert that 125 is the smallest possible Lipschitz constant.

Theorem 1.1 states the construction. Section 5 describes the Lean formalization and prior checks; Appendix B gives the certificate computation.

## Formalization

The supplied [Green15.lean](lean/Green15.lean) contains `main_result` and `target : fcTypeOfName% "Green15.green_15"`. Its header states that the validator supplies the trusted imports and enclosing `Bounty` namespace.

See the [Lean record](lean/README.md) for source availability, manuscript-reported checks, and materials needed to reproduce them. Repository compilation and mathematical review have not been performed.

## References and acknowledgments

The [original PDF](paper/proof.pdf) preserves the authors’ references and credits. The manuscript acknowledges substantial assistance from OpenAI Codex in the computational search, proof development, verification, formalization, and manuscript preparation.

## Revision notes

- **2026-09-15:** Added the supplied manuscript; no Lean counterpart was included in that upload. Original file contents were preserved byte for byte. See [the manuscript record](paper/README.md), [SHA256SUMS](SHA256SUMS), and the [upload inventory](../../docs/upload-inventory.md).
- **2026-09-15, subsequent upload:** Added `lean/Green15.lean` unchanged and recorded its declared target. Repository compilation remains pending.
