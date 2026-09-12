# anthropics/fermats-last-theorem: assessed, nothing reusable here

Checked 2026-09-05 at the user's suggestion ("if u want to steal code").
Shallow-cloned, surveyed, and **deleted** — it contains none of the
algebraic topology this campaign needs.

- 60,478 `.lean` files, Apache 2.0, toolchain `leanprover/lean4:v4.33.1`
  (this repo is pinned at v4.32.0, so nothing would import without a port).
- Layout is one theorem per file: `Theorems/Thm_<name>.lean`, plus
  `Definitions/`, `P2M/`, `verification/`, `FinalCheck.lean`.

Occurrence counts over the whole tree, for the things we actually need:

| we need | files containing it |
|---|---|
| Steenrod squares | **0** |
| Chern classes | **0** |
| Stiefel–Whitney classes | **0** |
| topological K-theory | **0** |
| Borsuk–Ulam | **0** |
| vector bundles | **0** |
| homotopy groups | **0** |
| complex projective space | **0** |

The large hits (`Cohomology` 3599, `singular` 8064, `CupProduct` 196) are
number-theoretic: Galois and group cohomology, singular points of schemes.
Different subject; none of it touches singular cohomology of a topological
space, characteristic classes, or K-theory.

**Do not re-clone it.** The clone is 1.8 GB and filled this machine's disk on
2026-09-05 (583 Mi free at the low point), which stalled every lane on ENOSPC
until it was removed. If a future lane wants to check something in it, use the
GitHub web view or a sparse checkout of a single path.

The vendored `GroupApproximation/ThirdParty/HamSandwich/` tree remains the
campaign's only external topology dependency, and it is the right one.
