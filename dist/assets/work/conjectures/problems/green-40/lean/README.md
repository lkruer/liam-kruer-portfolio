# Lean formalization — Green #40

[Back to the problem](../README.md) · [Verification guide](../../../docs/lean-verification.md)

**Status: Not uploaded.**

## Expected source and scope

Section 8 of the [manuscript](../paper/proof.pdf) names `Green40.lean` as the complete source, containing `Bounty.target` with type `True ↔ Green40.f 2 = 1`. It describes imports of the Green 40 problem module and `TaskSupport`.

The formal target concerns covering radius at most two. The paper’s additional observation about exact radius two is described separately in the proof of Theorem 1.1.

## Manuscript-reported environment and checks

The PDF reports Lean **4.33.1**, Formal Conjectures `8432eac998110a563e03df65a28c117e97c8c142`, and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

It reports local kernel and task-inspector checks of the target, with only `propext`, `Classical.choice`, and `Quot.sound` as axiom dependencies. The described source and verification records have not been supplied, and these checks have not been reproduced here.

## Repository verification record

| Field | Record |
| :--- | :--- |
| Source revision built | Not supplied |
| Build commands executed | None |
| Build result / kernel audit | Not run |
| Mathematical target correspondence | Not independently reviewed |
| File integrity | No Lean source supplied |

## Materials still needed

Supply `Green40.lean`, the original pinned project with `lean-toolchain`, Lake configuration and dependency manifest, `TaskSupport`, and the verification record and reproduction instructions described in Section 8.
