# Erdős #96

**Superlinearly many unit distances in convex position**

Liam Kruer and Jensen Kohlmeyer · September 9, 2026

[Read the proof](paper/proof.pdf) · [Lean sources and record](lean/) · [Submission notes](submission.md) · [All proofs](../../README.md#proof-index)

## Overview

| Field | Details |
| :--- | :--- |
| Official problem page | [Erdős #96](https://www.erdosproblems.com/96) |
| Contribution | Counterexample to the proposed linear bound (manuscript claim). |
| Manuscript | [PDF, 8 pages](paper/proof.pdf) |
| Manuscript date | September 9, 2026 |
| Manuscript review | Not independently reviewed in this repository |
| Lean | Uploaded; not checked |
| Submission | Draft; no announcement recorded |

## Problem and manuscript claim

Let $U_c(n)$ be the maximum number of unordered unit-distance pairs among $n$ points in strictly convex position in the Euclidean plane. The question is whether $U_c(n)=O(n)$.

The manuscript describes convex point sets whose number of unit-distance pairs divided by their cardinality is arbitrarily large, claiming a negative answer to the linear-bound question.

This description follows the supplied manuscript. Its mathematical correctness and correspondence to the current official problem have not been independently reviewed in this repository.

## Scope and reading guide

The claimed result concerns exact Euclidean unit distances and every vertex of the constructed convex set. The uploaded source is a single submission body; the PDF describes an additional project organized into 21 modules.

Theorem 1.1 and Corollary 1.2 state the construction and its consequence. Sections 2–6 give the argument; Section 7 describes the formal statement, project modules, and reported verification.

## Formalization

`target` for the negation of `Erdos96.erdos_96`.

See the [Lean record](lean/README.md) for the uploaded files, reported environment, and missing reproduction materials. Previously reported checks in the manuscript are recorded separately from checks performed in this repository.

## References and acknowledgments

References and author credits are preserved in the [original PDF](paper/proof.pdf). The manuscript acknowledges substantial assistance from OpenAI Codex in the mathematical development, formalization, and manuscript preparation. Its authors remain responsible for the mathematical content. Prior literature has not been reassessed during this upload.

## Revision notes

- **2026-09-13:** Added the supplied manuscript and supplied Lean source. PDF and source contents were preserved byte for byte. Original filenames are recorded in [the manuscript record](paper/README.md) and [upload inventory](../../docs/upload-inventory.md); [SHA256SUMS](SHA256SUMS) identifies the uploaded files.
