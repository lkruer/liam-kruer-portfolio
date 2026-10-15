# Erdős #14

**A uniform square-root lower bound for non-unique sums and a resolution of Erdős problem 14**

Liam Kruer and Jensen Kohlmeyer · September 13, 2026

[Read the proof](paper/proof.pdf) · [Lean sources and record](lean/) · [Submission notes](submission.md) · [All proofs](../../README.md#proof-index)

## Overview

| Field | Details |
| :--- | :--- |
| Official problem page | [Erdős #14](https://www.erdosproblems.com/14) |
| Contribution | Part I: affirmative answer; part II: negative answer (manuscript claims). |
| Manuscript | [PDF, 8 pages](paper/proof.pdf) |
| Manuscript date | September 13, 2026 |
| Manuscript review | Not independently reviewed in this repository |
| Lean | Uploaded; not checked |
| Submission | Draft; no announcement recorded |

## Problem and manuscript claim

For $A \subseteq \mathbb{N}_0$, let $E_A(N)$ count positive integers at most $N$ without exactly one unordered representation as a sum of two elements of $A$, allowing equal summands. Part I asks whether $N^{1/2-\varepsilon}=O(E_A(N))$ for every $A$ and every $\varepsilon>0$. Part II asks whether some $A$ has $E_A(N)=o(\sqrt{N})$.

The manuscript claims the uniform bound $\sqrt{N}<12000 E_A(N)$ for every $A$ and every integer $N\geq 2\cdot 10^{24}$. It uses this to answer part I affirmatively and part II negatively.

This description follows the supplied manuscript. Its mathematical correctness and correspondence to the current official problem have not been independently reviewed in this repository.

## Scope and reading guide

Both parts are covered by the unified PDF. The two supplied Lean files have separate final targets and duplicate the shared core; they should be checked separately in their respective task wrappers.

Theorem 1.1 gives the uniform bound; Corollaries 1.2 and 1.3 state the two answers. Sections 2–6 contain the argument, and Section 7 describes the supplied formalizations and the scope of previously reported checks.

## Formalization

`target` for `Erdos14.erdos_14.parts.i`; a separate `target` for the negation of `Erdos14.erdos_14.parts.ii`.

See the [Lean record](lean/README.md) for the uploaded files, reported environment, and missing reproduction materials. Previously reported checks in the manuscript are recorded separately from checks performed in this repository.

## References and acknowledgments

References and author credits are preserved in the [original PDF](paper/proof.pdf). The manuscript acknowledges substantial assistance from OpenAI Codex in the mathematical development, formalization, and manuscript preparation. Its authors remain responsible for the mathematical content. Prior literature has not been reassessed during this upload.

## Revision notes

- **2026-09-13:** Added the supplied manuscript and both supplied Lean proof bodies. PDF and source contents were preserved byte for byte. Original filenames are recorded in [the manuscript record](paper/README.md) and [upload inventory](../../docs/upload-inventory.md); [SHA256SUMS](SHA256SUMS) identifies the uploaded files.
- **2026-09-15:** Restored the unified manuscript and both Lean proof parts together in this problem folder. The PDF and Lean files match the previously uploaded versions.
