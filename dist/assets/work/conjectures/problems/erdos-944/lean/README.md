# Lean formalization — Erdős #944

[Back to the problem](../README.md) · [Verification guide](../../../docs/lean-verification.md)

**Status: Uploaded; not checked.**

## Supplied source

| File | Role | Lines |
| :--- | :--- | ---: |
| [erdos944.lean](erdos944.lean) | All-color existence target | 9,548 |

The supplied file includes its imports of `FormalConjectures.ErdosProblems.«944»` and `TaskSupport` and the enclosing `Bounty` namespace. The imported task project was not included. Section 8 calls the standalone file `Solution.lean`; the upload is preserved as `erdos944.lean`.

## Target and scope

`Bounty.target` for `Erdos944.erdos_944`.

Principal declarations observed in the supplied source: `Bounty.Erdos944Proof.erdos944_four`, `erdos944_five`, `erdos944_ge_six`, and `erdos944_all`.

This is the existence statement for all k ≥ 4 and r ≥ 1. The manuscript does not assert the stronger statement about every sufficiently large graph order. Its higher-color construction is credited to prior work.

## Reported environment and earlier checks

The manuscript reports Lean **4.33.1** (compiler commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`), Formal Conjectures `8432eac998110a563e03df65a28c117e97c8c142`, and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

Section 8 reports compilation and axiom checks for 570 theorems in a 9,548-line source. The supplied file has 9,548 lines. The reported `validation.json` and finite-check program were not included, and the reported checks have not been reproduced here. See the [manuscript, Section 8](../paper/proof.pdf).

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

The task project, `TaskSupport`, `validation.json`, and supplementary exact-arithmetic program described in the manuscript were not supplied.

No `lean-toolchain`, `lakefile.toml` / `lakefile.lean`, or `lake-manifest.json` was supplied with this problem. Add the original project or task bundle before recording an independently reproduced build. The uploaded proof text has not been edited to guess the missing environment.
