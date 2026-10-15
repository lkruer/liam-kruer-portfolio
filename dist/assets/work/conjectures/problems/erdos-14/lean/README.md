# Lean formalization — Erdős #14

[Back to the problem](../README.md) · [Verification guide](../../../docs/lean-verification.md)

**Status: Uploaded; not checked.**

## Supplied source

| File | Role | Lines |
| :--- | :--- | ---: |
| [Erdos14_PartI.lean](Erdos14_PartI.lean) | Part I, affirmative target | 1,233 |
| [Erdos14_PartII_Counterexample.lean](Erdos14_PartII_Counterexample.lean) | Part II, negated target | 1,167 |

Both files are submission bodies. Their headers say that the task supplies imports and the enclosing `Bounty` namespace. Section 7 identifies the Erdős 14 problem module and `TaskSupport`. These wrappers were not supplied. Each body must be checked separately because the files repeat the same core declarations and each defines `target`.

## Target and scope

`target` for `Erdos14.erdos_14.parts.i`; a separate `target` for the negation of `Erdos14.erdos_14.parts.ii`.

Principal declarations observed in the supplied source: `Erdos14Verification.uniform_sqrt_bound`, `Erdos14Verification.part_i_positive`, and `Erdos14Verification.part_ii_negative` in the respective sources.

Both parts are covered by the unified PDF. The two supplied Lean files have separate final targets and duplicate the shared core; they should be checked separately in their respective task wrappers.

## Reported environment and earlier checks

The manuscript reports Lean **4.33.1**, Formal Conjectures `8432eac998110a563e03df65a28c117e97c8c142`, mathlib `0df444a360eaa60ab8c11dca51a86af692955474`, and validator `076ead3c71c8b0bfc0641975076d95015d075ce3`.

Section 7 preserves compilation, target-type, axiom-audit, and replay results reported by the earlier part-specific manuscripts. It explicitly says the logs, verification JSON, and replay harness were unavailable for the unified revision and those checks were not rerun there. See the [manuscript, Section 7](../paper/proof.pdf).

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

Original task wrappers, pinned project configuration, verification JSON, and replay logs were not included in this upload.

No `lean-toolchain`, `lakefile.toml` / `lakefile.lean`, or `lake-manifest.json` was supplied with this problem. Add the original project or task bundle before recording an independently reproduced build. The uploaded proof text has not been edited to guess the missing environment.
