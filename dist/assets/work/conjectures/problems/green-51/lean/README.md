# Lean formalization — Green #51

[Back to the problem](../README.md) · [Verification guide](../../../docs/lean-verification.md)

**Status: Uploaded; not checked.**

## Supplied source

[green51onehalf.lean](green51onehalf.lean) — 1,925 lines. The original filename and contents are preserved. The manuscript calls the main proof `Solution.lean`; the supplied file is retained under its uploaded name.

The source includes `import FormalConjectures.GreensOpenProblems.«51»`, `import TaskSupport`, and the enclosing `Bounty` namespace.

## Target and scope

The source declares `Bounty.target : fcTypeOfName% "Green51.green_51.one_half"`, proved using `Green51Proof.green_one_half`.

The one-half-density question only. The manuscript does not determine the optimal guaranteed dimension at every density or claim optimal constants.

## Manuscript-reported environment and checks

Section 7 reports Lean **4.33.1**, Formal Conjectures `8432eac998110a563e03df65a28c117e97c8c142`, and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

The manuscript reports compilation, target inspection, dependency/axiom checks, and static submission checks for three Lean files. The main source is now present; the companion files and report were not included. See the [manuscript, Section 7](../paper/proof.pdf).

## Repository verification record

| Field | Record |
| :--- | :--- |
| Source revision built | Not checked |
| Build commands executed | None |
| Build result / kernel audit | Not run |
| Mathematical target correspondence | Not independently reviewed |
| File integrity | Original uploaded source preserved; checksum in [SHA256SUMS](../SHA256SUMS). |

## Materials still needed

The main proof is present as `green51onehalf.lean`. The manuscript’s `PaperTheorem.lean`, `CheckGreen51.lean`, pinned task project with `TaskSupport`, and companion verification report remain to be supplied.

No `lean-toolchain`, Lake project file, or dependency manifest was included. Add the original environment and support files before recording an independently reproduced build.
