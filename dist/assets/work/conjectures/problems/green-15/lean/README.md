# Lean formalization — Green #15

[Back to the problem](../README.md) · [Verification guide](../../../docs/lean-verification.md)

**Status: Uploaded; not checked.**

## Supplied source

[Green15.lean](Green15.lean) — 514 lines. The original filename and contents are preserved. The file is a submission body without imports or an outer namespace; its header states that the validator supplies trusted imports and the enclosing `Bounty` namespace.

## Target and scope

The source declares `main_result` and `target : fcTypeOfName% "Green15.green_15"`. With the wrapper described in its header, the latter is `Bounty.target`. The declared main result includes strict monotonicity, the permitted increments, a Lipschitz constant of 125, and a graph free of nontrivial three-term arithmetic progressions.

The claimed construction concerns the full existence question for a Lipschitz graph. The manuscript does not assert that 125 is the smallest possible Lipschitz constant.

## Manuscript-reported environment and checks

Section 5 and the uploaded source header report Lean **4.33.1** and Formal Conjectures `8432eac998110a563e03df65a28c117e97c8c142`.

The manuscript reports kernel checks of the finite invariant, an axiom audit, and static submission-policy checks using the trusted task header and footer. The main source is now present; those wrapper files and validation records were not uploaded. See the [manuscript, Section 5](../paper/proof.pdf).

## Repository verification record

| Field | Record |
| :--- | :--- |
| Source revision built | Not checked |
| Build commands executed | None |
| Build result / kernel audit | Not run |
| Mathematical target correspondence | Not independently reviewed |
| File integrity | Original uploaded source preserved; checksum in [SHA256SUMS](../SHA256SUMS). |

## Materials still needed

The main proof is present. The trusted `SolutionHeader.lean.txt` and `SolutionFooter.lean.txt`, original task/project configuration, and validation record remain to be supplied.

No `lean-toolchain`, Lake project file, or dependency manifest was included. Add the original environment and support files before recording an independently reproduced build.
