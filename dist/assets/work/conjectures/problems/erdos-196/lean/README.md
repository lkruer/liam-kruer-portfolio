# Lean formalization — Erdős #196

[Back to the problem](../README.md) · [Verification guide](../../../docs/lean-verification.md)

**Status: Uploaded; not checked.**

## Supplied source

| File | Role | Lines |
| :--- | :--- | ---: |
| [Erdos196.lean](Erdos196.lean) | Counterexample submission body | 635 |

Despite the supplied filename, this file omits imports and the outer namespace. Its header specifies `FormalConjectures.ErdosProblems.«196»`, `TaskSupport`, and an enclosing `Bounty` namespace supplied by the validator. That wrapper was not included.

## Target and scope

`target` for the negation of `Erdos196.erdos_196`.

Principal declarations observed in the supplied source: `Construction196.permFun`, `Construction196.permFun_no_four`, and `Construction196.counterexample`.

The claimed permutation enumerates all natural numbers and avoids both directions of monotone four-term progressions. The supplied Lean file is the body intended for the counterexample task wrapper.

## Reported environment and earlier checks

The manuscript and source identify Formal Conjectures `8432eac998110a563e03df65a28c117e97c8c142`; the manuscript reports Lean **4.33.1**. A dependency manifest was not supplied.

Section 7 reports compilation, exact-target inspection, and axiom checks for a standalone companion and a submission body. The uploaded file contains the counterexample body; the separately described `Bounty.paper_main` declaration is not present in this file. See the [manuscript, Section 7](../paper/proof.pdf).

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

The standalone companion, wrapper, dependency manifest, and supplementary archive with verification results were not included.

No `lean-toolchain`, `lakefile.toml` / `lakefile.lean`, or `lake-manifest.json` was supplied with this problem. Add the original project or task bundle before recording an independently reproduced build. The uploaded proof text has not been edited to guess the missing environment.
