# Erdős #944

**Vertex-critical four-chromatic graphs with no small critical edge set**

Liam Kruer and Jensen Kohlmeyer · September 10, 2026

[Read the proof](paper/proof.pdf) · [Lean sources and record](lean/) · [Submission notes](submission.md) · [All proofs](../../README.md#proof-index)

## Overview

| Field | Details |
| :--- | :--- |
| Official problem page | [Erdős #944](https://www.erdosproblems.com/944) |
| Contribution | Four-color construction and all-color existence statement (manuscript claims). |
| Manuscript | [PDF, 13 pages](paper/proof.pdf) |
| Manuscript date | September 10, 2026 |
| Manuscript review | Not independently reviewed in this repository |
| Lean | Uploaded; not checked |
| Submission | Draft; no announcement recorded |

## Problem and manuscript claim

For every $k\geq4$ and $r\geq1$, does there exist a finite $k$-chromatic vertex-critical graph whose chromatic number remains $k$ after deleting any set of at most $r$ edges?

The manuscript claims a four-color construction and combines it with the higher-color result attributed to Skottova and Steiner. The supplied Lean source targets the existence statement for every k ≥ 4.

This description follows the supplied manuscript. Its mathematical correctness and correspondence to the current official problem have not been independently reviewed in this repository.

## Scope and reading guide

This is the existence statement for all k ≥ 4 and r ≥ 1. The manuscript does not assert the stronger statement about every sufficiently large graph order. Its higher-color construction is credited to prior work.

Theorem 1.1 states the four-color construction and Corollary 1.2 gives all-color existence. Sections 2–7 develop the construction; Section 8 covers the formalization, prior higher-color result, and reported checks.

## Formalization

`Bounty.target` for `Erdos944.erdos_944`.

See the [Lean record](lean/README.md) for the uploaded files, reported environment, and missing reproduction materials. Previously reported checks in the manuscript are recorded separately from checks performed in this repository.

## References and acknowledgments

References and author credits are preserved in the [original PDF](paper/proof.pdf). The manuscript acknowledges substantial assistance from OpenAI Codex in the mathematical development, formalization, and manuscript preparation. Its authors remain responsible for the mathematical content. Prior literature has not been reassessed during this upload.

## Revision notes

- **2026-09-13:** Added the supplied manuscript and supplied Lean source. PDF and source contents were preserved byte for byte. Original filenames are recorded in [the manuscript record](paper/README.md) and [upload inventory](../../docs/upload-inventory.md); [SHA256SUMS](SHA256SUMS) identifies the uploaded files.
