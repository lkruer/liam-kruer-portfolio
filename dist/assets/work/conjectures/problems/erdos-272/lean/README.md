# Lean formalization — Erdős #272

[Back to the problem](../README.md) · [Verification guide](../../../docs/lean-verification.md)

**Status: Uploaded; not checked.**

## Supplied source

| File | Role | Lines |
| :--- | :--- | ---: |
| [Main.lean](Main.lean) | Szabó strong variant; submission body | 12,791 |

The upload is preserved as `Main.lean`, with its original filename and bytes. It has no imports or enclosing `Bounty` namespace. The PDF describes this submission-body format as `submission/Main.lean`; the trusted task wrapper supplies `FormalConjectures.ErdosProblems.«272»`, `TaskSupport`, and the outer namespace. The standalone companion is called `Solution.lean` in the manuscript.

## Target and scope

The final declaration in the supplied source is:

```lean
theorem target : fcTypeOfName% "Erdos272.erdos_272.variants.szabo_strong" := by
  exact target_of_structural_reduction structural_reduction
```

Principal declarations observed in the source include `target_of_finite_upper_bound`, `target_of_structural_reduction`, and `structural_reduction`. The original wrapper would place these declarations in `Bounty`.

The manuscript addresses the Szabó strong variant. It does not claim an exact formula, the optimal linear coefficient, or a classification of every extremal family. The declared target matches the variant identified by the manuscript; its type and proof have not been independently checked here.

## Reported environment and earlier checks

Section 10 and the uploaded source header both report Lean **4.33.1**, Formal Conjectures `8432eac998110a563e03df65a28c117e97c8c142`, and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The project configuration was not supplied.

Section 10 describes compilation, axiom, type, dependency, and static-policy checks for a 12,797-line standalone file. The uploaded submission body has 12,791 lines and omits its wrapper. The verification record was not supplied, and these checks have not been reproduced here. See the [manuscript, Section 10](../paper/proof.pdf).

## Repository verification record

| Field | Record |
| :--- | :--- |
| Source revision built | Not checked |
| Build commands executed | None |
| Build result | Not run |
| Kernel / axiom audit | Not run |
| Target correspondence | Not independently reviewed |
| File integrity | Uploaded source bytes matched the original `Main.lean`; see [SHA256SUMS](../SHA256SUMS). |

## Materials still needed for reproduction

The primary Lean counterpart is now present. The original task wrapper, `TaskSupport`, pinned project, and `verification.json` were not supplied. The standalone companion and source TeX described by the PDF are also absent from this upload.

No `lean-toolchain`, `lakefile.toml` / `lakefile.lean`, or `lake-manifest.json` was supplied with this problem. Add the original project or task bundle before recording an independently reproduced build. The uploaded proof text has not been edited to guess the missing environment.

The PDF gives the wrapped standalone `Solution.lean` SHA-256 as:

```text
0d651c16942333977ee1ee4ddf17d017e3510f0dc6f2f1dd3542e434d16eb91e
```

This manuscript-reported checksum refers to the standalone file with its wrapper. It is not the checksum of the uploaded submission body; the latter is recorded separately in [SHA256SUMS](../SHA256SUMS).
