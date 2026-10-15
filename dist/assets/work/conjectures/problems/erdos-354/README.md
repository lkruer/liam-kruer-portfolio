# Erdős #354

**Completeness of Two Floor-Doubling Sequences**

Jensen Kohlmeyer and Liam Kruer · September 11, 2026

[Read the proof](paper/proof.pdf) · [Lean sources and record](lean/) · [Submission notes](submission.md) · [All proofs](../../README.md#proof-index)

## Overview

| Field | Details |
| :--- | :--- |
| Official problem page | [Erdős #354](https://www.erdosproblems.com/354) |
| Contribution | Part I, multiplier 2: affirmative answer (manuscript claim). |
| Manuscript | [PDF, 13 pages](paper/proof.pdf) |
| Manuscript date | September 11, 2026 |
| Manuscript review | Not independently reviewed in this repository |
| Lean | Uploaded; not checked |
| Submission | Draft; no announcement recorded |

## Problem and manuscript claim

For positive $\alpha,\beta$ with irrational $\alpha/\beta$, are all sufficiently large integers sums of distinct indexed terms from the sequences $\lfloor 2^n\alpha\rfloor$ and $\lfloor 2^n\beta\rfloor$?

The manuscript claims completeness of the two floor-doubling sequences, with each index usable at most once and equal values at different indices remaining separate available terms.

This description follows the supplied manuscript. Its mathematical correctness and correspondence to the current official problem have not been independently reviewed in this repository.

## Scope and reading guide

The PDF and supplied Lean target cover part I with multiplier 2. The separate question about a multiplier in (1, 2) is outside this manuscript’s scope.

Theorem 1.1 states the result and its indexing convention. The main argument uses symbolic tower systems and binary carries; Section 8 maps the proof to its Lean source blocks and reported checks.

## Formalization

`Bounty.target` for `Erdos354.erdos_354.parts.i`.

See the [Lean record](lean/README.md) for the uploaded files, reported environment, and missing reproduction materials. Previously reported checks in the manuscript are recorded separately from checks performed in this repository.

## References and acknowledgments

References and author credits are preserved in the [original PDF](paper/proof.pdf). The manuscript acknowledges substantial assistance from OpenAI Codex in the mathematical development, formalization, and manuscript preparation. Its authors remain responsible for the mathematical content. Prior literature has not been reassessed during this upload.

## Revision notes

- **2026-09-13:** Added the supplied manuscript and supplied Lean source. PDF and source contents were preserved byte for byte. Original filenames are recorded in [the manuscript record](paper/README.md) and [upload inventory](../../docs/upload-inventory.md); [SHA256SUMS](SHA256SUMS) identifies the uploaded files.
