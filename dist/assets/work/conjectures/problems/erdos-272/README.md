# Erdős #272

**A linear error bound for Erdős problem 272**

Jensen Kohlmeyer and Liam Kruer · September 9, 2026

[Read the proof](paper/proof.pdf) · [Lean sources and record](lean/) · [Submission notes](submission.md) · [All proofs](../../README.md#proof-index)

## Overview

| Field | Details |
| :--- | :--- |
| Official problem page | [Erdős #272](https://www.erdosproblems.com/272) |
| Contribution | Szabó strong variant: a linear error term (manuscript claim). |
| Manuscript | [PDF, 15 pages](paper/proof.pdf) |
| Manuscript date | September 9, 2026 |
| Manuscript review | Not independently reviewed in this repository |
| Lean | Uploaded; not checked |
| Submission | Draft; no announcement recorded |

## Problem and manuscript claim

Let $t(N)$ be the largest size of a family of subsets of $\{1,\ldots,N\}$ whose intersections of distinct members are nonempty arithmetic progressions. The Szabó strong variant asks for $t(N)=N^2/2+O(N)$.

The manuscript claims $\binom{N}{2}+1\leq t(N)\leq N^2/2+30000N$ for all sufficiently large $N$, yielding the linear error term.

This description follows the supplied manuscript. Its mathematical correctness and correspondence to the current official problem have not been independently reviewed in this repository.

## Scope and reading guide

The manuscript addresses the Szabó strong variant. It does not claim an exact formula, the optimal linear coefficient, or a classification of every extremal family. The supplied Lean source is the submission body for this variant.

Theorem 1.1 states the bounds. Sections 2–9 develop and assemble the counting argument; Section 10 describes the Lean certificate and its reported checks.

## Formalization

The supplied [Main.lean](lean/Main.lean) ends with `target : fcTypeOfName% "Erdos272.erdos_272.variants.szabo_strong"`, proved using `target_of_structural_reduction structural_reduction`. The task wrapper supplies the imports and enclosing `Bounty` namespace.

See the [Lean record](lean/README.md) for the uploaded files, reported environment, and missing reproduction materials. Previously reported checks in the manuscript are recorded separately from checks performed in this repository.

## References and acknowledgments

References and author credits are preserved in the [original PDF](paper/proof.pdf). The manuscript acknowledges substantial assistance from OpenAI Codex in the mathematical development, formalization, and manuscript preparation. Its authors remain responsible for the mathematical content. Prior literature has not been reassessed during this upload.

## Revision notes

- **2026-09-13:** Added the supplied manuscript and a record of the missing Lean counterpart. PDF and source contents were preserved byte for byte. Original filenames are recorded in [the manuscript record](paper/README.md) and [upload inventory](../../docs/upload-inventory.md); [SHA256SUMS](SHA256SUMS) identifies the uploaded files.
- **2026-09-13, subsequent upload:** Added `lean/Main.lean` unchanged, confirmed the declared #272 Szabó strong target, and updated the inventory and checksum record. Repository compilation and proof verification remain pending.
