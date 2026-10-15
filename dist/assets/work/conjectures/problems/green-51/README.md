# Green #51

**Green’s Open Problem 51 at Density One Half: Bounded Codimension in Binary Sumsets**

Jensen Kohlmeyer and Liam Kruer · September 2026

[Read the proof](paper/proof.pdf) · [Lean source record](lean/) · [Submission notes](submission.md) · [All proofs](../../README.md#proof-index)

## Overview

| Field | Details |
| :--- | :--- |
| Collection | [Ben Green, *100 open problems*](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf), Problem 51 |
| Contribution | The density-one-half question (manuscript claim). |
| Manuscript | [PDF, 7 pages](paper/proof.pdf) |
| Manuscript date | September 2026 |
| Manuscript review | Not independently reviewed in this repository |
| Lean | Uploaded; not checked |
| Submission | Draft; no announcement recorded |

## Problem and manuscript claim

For each fixed $k>0$, does density at least $1/2-k/\sqrt n$ in $\mathbb{F}_2^n$ guarantee that the sumset contains a subspace of codimension bounded independently of $n$?

The manuscript claims that density at least $1/2-\varepsilon$, for $0\leq\varepsilon\leq1/4$, guarantees a linear subspace in $A+A$ of codimension at most $1+256e n\varepsilon^2$. It derives a bound depending only on $k$ for the specified one-half-density question.

## Scope and reading guide

The one-half-density question only. The manuscript does not determine the optimal guaranteed dimension at every density or claim optimal constants.

Theorem 1.1 states the quantitative bound and Corollary 1.2 gives the one-half-density consequence. Section 7 describes the formalization and companion files.

## Formalization

The supplied [green51onehalf.lean](lean/green51onehalf.lean) contains `Bounty.target : fcTypeOfName% "Green51.green_51.one_half"`, proved using `Green51Proof.green_one_half`. It includes imports for the formal problem and `TaskSupport`; the original uploaded filename is preserved.

See the [Lean record](lean/README.md) for source availability, manuscript-reported checks, and materials needed to reproduce them. Repository compilation and mathematical review have not been performed.

## References and acknowledgments

The [original PDF](paper/proof.pdf) preserves the authors’ references and credits. The manuscript thanks Grant Huffman for a helpful insight and acknowledges substantial assistance from OpenAI Codex in mathematical development, formalization, verification, and manuscript preparation.

## Revision notes

- **2026-09-15:** Added the supplied manuscript; no Lean counterpart was included in that upload. Original file contents were preserved byte for byte. See [the manuscript record](paper/README.md), [SHA256SUMS](SHA256SUMS), and the [upload inventory](../../docs/upload-inventory.md).
- **2026-09-15, subsequent upload:** Added `lean/green51onehalf.lean` unchanged and recorded its declared one-half-density target. Repository compilation remains pending.
