# Lean formalization — Erdős #354

[Back to the problem](../README.md) · [Verification guide](../../../docs/lean-verification.md)

**Status: Uploaded; not checked.**

## Supplied source

| File | Role | Lines |
| :--- | :--- | ---: |
| [Erdos354.lean](Erdos354.lean) | Part I; supplied as an extensionless Lean file | 10,160 |

The supplied file already imports `FormalConjectures.ErdosProblems.«354»` and `TaskSupport`, and includes its `Bounty` namespace. Its external imports still require the original task project. The extensionless upload `lean354` is stored here as `Erdos354.lean` with identical bytes.

## Target and scope

`Bounty.target` for `Erdos354.erdos_354.parts.i`.

Principal declarations observed in the supplied source: `Bounty.Erdos354Formal.full_target_of_symbolic_digit_criteria`, `symbolicallyDisjoint_of_boundedZeroRuns`, and `forwardTransport_of_not_symbolicallyDisjoint`.

The PDF and supplied Lean target cover part I with multiplier 2. The separate question about a multiplier in (1, 2) is outside this manuscript’s scope.

## Reported environment and earlier checks

The manuscript reports Lean **4.33.1**, Formal Conjectures `8432eac998110a563e03df65a28c117e97c8c142`, mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and validator `922a912f3777ac11451e2d145356e78de4dbedb2`.

Section 8 reports compilation, static checks, target inspection, and an axiom audit for the standalone and wrapped submissions. It names `Challenge.lean` as the standalone source; the uploaded source has been preserved under the descriptive repository filename. See the [manuscript, Section 8](../paper/proof.pdf).

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

The pinned task project, `TaskSupport`, `Audit.lean`, `verify.py`, and `verification.json` described in the manuscript were not supplied.

No `lean-toolchain`, `lakefile.toml` / `lakefile.lean`, or `lake-manifest.json` was supplied with this problem. Add the original project or task bundle before recording an independently reproduced build. The uploaded proof text has not been edited to guess the missing environment.
