# Lean formalization — Erdős #96

[Back to the problem](../README.md) · [Verification guide](../../../docs/lean-verification.md)

**Status: Uploaded; not checked.**

## Supplied source

| File | Role | Lines |
| :--- | :--- | ---: |
| [erdos96.lean](erdos96.lean) | Counterexample submission body | 2,338 |

The file has no imports and its header says the task supplies imports and the enclosing `Bounty` namespace. It opens `_root_.Erdos96` and uses `fcTypeOfName%`, so the original problem definitions and task support are required. The wrapper was not supplied.

## Target and scope

`target` for the negation of `Erdos96.erdos_96`.

Principal declarations observed in the supplied source: `Proof.plane_counterexample`, `Proof.large_convex_counterexample`, and `Proof.erdos_96_false`.

The claimed result concerns exact Euclidean unit distances and every vertex of the constructed convex set. The uploaded source is a single submission body; the PDF describes an additional project organized into 21 modules.

## Reported environment and earlier checks

The manuscript reports Lean **4.33.1**, mathlib release **v4.33.1** at `0df444a360eaa60ab8c11dca51a86af692955474`, and upstream problem-definition revision `b82b08faa9006484021c12005ab41287fb2ffb69`. These describe the PDF’s project; the exact wrapper revision for the uploaded submission body has not been established.

Section 7 reports a warnings-as-failures build, an axiom audit, and kernel replay for a 21-module project. The supplied file instead contains the assembled submission body, with `Proof` declaration names. The original project and logs are not included, so that correspondence has not been reproduced here. See the [manuscript, Section 7](../paper/proof.pdf).

## Repository verification record

| Field | Record |
| :--- | :--- |
| Source revision built | Not checked |
| Build commands executed | None |
| Build result | Not run |
| Kernel / axiom audit | Not run |
| Target correspondence | Not independently reviewed |
| File integrity | Uploaded source bytes matched the original files; see [SHA256SUMS](../SHA256SUMS). |

## Materials still needed for reproduction

The original project archive, including `Erdos96/ProblemDefinitions.lean`, `Audit.lean`, its manifest, wrapper, and verification logs, was not included.

No `lean-toolchain`, `lakefile.toml` / `lakefile.lean`, or `lake-manifest.json` was supplied with this problem. Add the original project or task bundle before recording an independently reproduced build. The uploaded proof text has not been edited to guess the missing environment.
