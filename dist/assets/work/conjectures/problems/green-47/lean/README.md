# Lean formalization — Green #47

[Back to the problem](../README.md) · [Verification guide](../../../docs/lean-verification.md)

**Status: Uploaded; not checked.**

## Supplied source

[Green47-COUNTEREXAMPLE-UPLOAD.lean](Green47-COUNTEREXAMPLE-UPLOAD.lean) — 553 lines. The original filename and contents are preserved. The file contains no imports or outer `Bounty` namespace; it relies on the task wrapper described in the manuscript. Its last declaration targets the negation of `Green47.green_47`.

## Target and scope

`target : ¬ (fcTypeOfName% "Green47.green_47")`, observed in the uploaded source. The task wrapper supplies the enclosing `Bounty` namespace.

Exact containment only. Both the PDF and the uploaded Lean header explicitly say this does not refute the formulation allowing finitely many exceptional elements, including Green and Harper’s Conjecture 1.7.

## Manuscript-reported environment and checks

Section 6 reports Lean **4.33.1**, mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, Formal Conjectures `8432eac998110a563e03df65a28c117e97c8c142`, and validator `922a912f3777ac11451e2d145356e78de4dbedb2`. The PDF describes the Formal Conjectures revision as a reconstructed task pin.

The manuscript reports local compilation, target-type checks, an axiom audit, and static policy checks. It explicitly separates these from the production comparator and kernel-replay pipeline, which its reported local run did not execute. See the [manuscript, Section 6](../paper/proof.pdf).

## Repository verification record

| Field | Record |
| :--- | :--- |
| Source revision built | Not checked |
| Build commands executed | None |
| Build result / kernel audit | Not run |
| Mathematical target correspondence | Not independently reviewed |
| File integrity | Original uploaded source preserved; checksum in [SHA256SUMS](../SHA256SUMS). |

## Materials still needed

The main submission body is present. The original task wrapper, problem definitions, `TaskSupport`, pinned project, standalone companion, and verification reports were not included.

No `lean-toolchain`, Lake project file, or dependency manifest was included. Add the original environment and support files before recording an independently reproduced build.
