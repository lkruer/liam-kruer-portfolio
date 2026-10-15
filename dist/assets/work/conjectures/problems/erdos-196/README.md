# Erdős #196

**Erdős 196: A permutation of the natural numbers with no monotone four-term arithmetic progression**

Jensen Kohlmeyer and Liam Kruer · September 9, 2026

[Read the proof](paper/proof.pdf) · [Lean sources and record](lean/) · [Submission notes](submission.md) · [All proofs](../../README.md#proof-index)

## Overview

| Field | Details |
| :--- | :--- |
| Official problem page | [Erdős #196](https://www.erdosproblems.com/196) |
| Contribution | Counterexample to the four-term progression assertion (manuscript claim). |
| Manuscript | [PDF, 7 pages](paper/proof.pdf) |
| Manuscript date | September 9, 2026 |
| Manuscript review | Not independently reviewed in this repository |
| Lean | Uploaded; not checked |
| Submission | Draft; no announcement recorded |

## Problem and manuscript claim

The problem asks whether every permutation of the natural numbers contains an increasing or decreasing four-term arithmetic progression as a subsequence.

The manuscript claims a bijection $p:\mathbb{N}_0\to\mathbb{N}_0$ with no indices $i<j<k<\ell$ satisfying both $p(i)+p(k)=2p(j)$ and $p(j)+p(\ell)=2p(k)$.

This description follows the supplied manuscript. Its mathematical correctness and correspondence to the current official problem have not been independently reviewed in this repository.

## Scope and reading guide

The claimed permutation enumerates all natural numbers and avoids both directions of monotone four-term progressions. The supplied Lean file is the body intended for the counterexample task wrapper.

Theorem 1.1 states the result. Sections 2–5 develop the finite extension argument, Section 6 builds the permutation, and Section 7 discusses formalization and reproducibility.

## Formalization

`target` for the negation of `Erdos196.erdos_196`.

See the [Lean record](lean/README.md) for the uploaded files, reported environment, and missing reproduction materials. Previously reported checks in the manuscript are recorded separately from checks performed in this repository.

## References and acknowledgments

References and author credits are preserved in the [original PDF](paper/proof.pdf). The manuscript acknowledges substantial assistance from OpenAI Codex in the mathematical development, formalization, and manuscript preparation. Its authors remain responsible for the mathematical content. Prior literature has not been reassessed during this upload.

## Revision notes

- **2026-09-13:** Added the supplied manuscript and supplied Lean source. PDF and source contents were preserved byte for byte. Original filenames are recorded in [the manuscript record](paper/README.md) and [upload inventory](../../docs/upload-inventory.md); [SHA256SUMS](SHA256SUMS) identifies the uploaded files.
