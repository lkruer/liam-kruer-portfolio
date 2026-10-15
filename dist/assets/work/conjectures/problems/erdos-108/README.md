# Erdős #108

**A counterexample to Erdős problem 108 via arc graphs**

Jensen Kohlmeyer and Liam Kruer · September 15, 2026

[Read the proof](paper/proof.pdf) · [Lean source](lean/Erdos108.lean) · [Verification record](lean/) · [Submission notes](submission.md) · [All proofs](../../README.md#proof-index)

## Overview

| Field | Details |
| :--- | :--- |
| Problem page | [Erdős #108](https://www.erdosproblems.com/108) |
| Contribution | Counterexample via arc graphs (manuscript claim). |
| Manuscript | [PDF, 8 pages](paper/proof.pdf) |
| Manuscript date | September 15, 2026 |
| Manuscript review | Not independently reviewed in this repository |
| Lean | Uploaded; not checked |
| Submission | Draft; no announcement recorded |

## Result and scope

The manuscript claims finite nonempty triangle-free graphs with arbitrarily large chromatic number whose ordinary four-cycle-free subgraphs are all six-colorable. It derives a counterexample at girth five and chromatic number seven. The source’s final reduction targets the negation of `Erdos108.erdos_108`.

Theorem 1.1 states the graph construction, Corollary 1.2 gives the consequence for Problem 108, and Section 5 describes the formalization. The manuscript does not claim that six is the smallest possible uniform bound.

This description follows the uploaded materials. Compilation, mathematical correctness, and correspondence to the intended problem statement have not been independently checked in this repository.

## Formalization

The uploaded [Erdos108.lean](lean/Erdos108.lean) contains 1,846 lines and ends with:

```lean
theorem target : ¬ (fcTypeOfName% "Erdos108.erdos_108") := by
  exact counterexample_of_family counterexample_family
```

The file contains no imports; the original imports or task wrapper and pinned project are needed to reproduce a build. See the [verification record](lean/README.md).

**Source correspondence:** Section 5 and Table 1 of the PDF reference `paper_main` and `arcGraph_triangle_free`, which do not occur in the currently uploaded Lean source. A matching source revision or clarification is still needed.

## References and acknowledgments

The [original PDF](paper/proof.pdf) preserves the authors’ references and credits, including the multipartite construction of Janzer, Steiner, and Sudakov. It acknowledges substantial OpenAI ChatGPT/Codex assistance in mathematical development, formalization, and manuscript preparation.

## Revision notes

- **2026-09-15:** Added the supplied Lean source unchanged, before its PDF was supplied. [SHA256SUMS](SHA256SUMS) records the original file checksums.
- **2026-09-15, subsequent upload:** Added `erdos108-arc-graphs.pdf` unchanged as `paper/proof.pdf`, recorded its title and authors, and noted the manuscript/source declaration discrepancy.
