# Lean formalization — Erdős #108

[Back to the problem](../README.md) · [Verification guide](../../../docs/lean-verification.md)

**Status: Uploaded; not checked.**

## Supplied source

[Erdos108.lean](Erdos108.lean) — 1,846 lines. The original filename and file contents are preserved.

The declarations `arc_counterexample_family` and `counterexample_family` construct the stated graph family. `counterexample_of_family` provides the final logical reduction, and `target` asserts `¬ (fcTypeOfName% "Erdos108.erdos_108")`.

## Manuscript correspondence

Section 5 and Table 1 of the [PDF](../paper/proof.pdf) refer to `Bounty.paper_main` and `Bounty.arcGraph_triangle_free`. Neither `paper_main` nor `arcGraph_triangle_free` occurs in the supplied 1,846-line source. The displayed final `target` declaration does agree with the uploaded file. A matching source revision or clarification of those additional declarations is still needed.

## Manuscript-reported environment and checks

Section 5 reports Lean **4.33.1**, mathlib revision `0df444a360ea`, and Formal Conjectures task revision `8432eac99811`. The PDF says the full revisions and artifact digest are in a separate verification record, which was not supplied.

The manuscript reports compilation with the trusted task wrapper, target-type and static-policy checks, and an axiom audit listing `propext`, `Classical.choice`, and `Quot.sound`. These are manuscript-reported checks; they have not been reproduced here or tied to the uploaded source by the missing artifact digest.

## Verification record

| Field | Record |
| :--- | :--- |
| Source revision built | Not checked |
| Build commands executed | None |
| Build result / kernel audit | Not run |
| Lean and dependency versions | Reported in the manuscript; project configuration and full revision record not supplied |
| Mathematical target correspondence | Not independently reviewed |
| Manuscript coverage | Not independently assessed; two named declarations are absent from this upload |
| File integrity | Original contents preserved; checksum in [SHA256SUMS](../SHA256SUMS). |

## Reproduction materials

The source contains no imports and relies on external definitions and the `fcTypeOfName%` macro. Supply the source revision corresponding to the manuscript or clarify the two absent declaration names, plus the original imports or task wrapper, relevant problem definitions and support, `lean-toolchain`, Lake configuration, dependency manifest, and the verification record with the checked artifact digest.
