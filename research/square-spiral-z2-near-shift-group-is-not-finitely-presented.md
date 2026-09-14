---
rg: 2
id: square-spiral-z2-near-shift-group-is-not-finitely-presented
kind: claim
title: For the square spiral enumeration of Z^2 the near shift group R_nu is metabelian and not finitely presented, so its shell germ group and one-singularity stabilizer are not finitely presented
distinct_from:
  square-spiral-z2-enumeration-passes-the-finite-window-gate: that proves the ascending gate clause for this enumeration; this proves that the other clause, finite presentation of R_nu, fails, so the enumeration dies at R_nu and not at the gate.
  one-ended-shell-inputs-admit-no-shift-normalizing-enumeration: that is an obstruction to window width zero for all one-ended inputs and all enumerations; this is a finite presentation obstruction for one explicit enumeration of Z^2.
  shell-prefix-core-detects-finite-ray-enumerations: that classifies when the prefix germ has a nontrivial normal core; this obstructs finite presentation of the near shift group itself, through an ascending splitting argument.
artifacts:
  - research/artifacts/hl-bh-universal-2-2026-09-13.md
  - research/artifacts/hl-bh-universal-2-2026-09-13/vectors.json
  - research/artifacts/hl-bh-universal-2-2026-09-13/verify.json
---

**ESTABLISHED** by `square-spiral-z2-near-shift-group-not-fp-proof` (not independently
reviewed; no novelty claimed).

## Statement

Let `nu` be the square spiral enumeration of `Z^2` and `sigma` its successor map (the
four-piece translation of `square-spiral-z2-enumeration-passes-the-finite-window-gate`). Let
`R_nu = <lambda(Z^2), s>` be the near permutation group of
`shell-germ-group-has-index-two-fiber-product`, identified with `<L_e1, L_e2, sigma>` acting
on `Z^2` modulo finitary permutations.

1. **Metabelian.** Let `D` be the group of near permutations that, at all but finitely many
   points, are finite products of *diagonal line shifts*. A diagonal line shift moves every
   far point of one half-line `{x - y = c, x + y > 0}`, `{x - y = c, x + y < 0}`,
   `{x + y = c, x - y > 0}` or `{x + y = c, x - y < 0}` by one diagonal step along it. `D`
   is abelian and normalized by `R_nu`, and the derived subgroup `R_nu'` lies in `D`. So
   `R_nu` is a finitely generated metabelian group.
2. **Not finitely presented.** `R_nu` is not finitely presented.
3. **Consequences for this enumeration.**
   - The shell germ group `Q` is not finitely presented, since `Q` finitely presented forces
     `R_nu` finitely presented (`shell-germ-fp-is-an-ascending-hnn-gate`).
   - `F_nu = R_nu x_Z R_nu` is not finitely presented.
   - The one-singularity stabilizer `A_1` of the shell envelope is not finitely presented
     (`shell-germ-group-has-index-two-fiber-product`).

Together with `square-spiral-z2-enumeration-passes-the-finite-window-gate`, the exact
failing clause for this enumeration is finite presentation of `R_nu`, not the ascending gate.

## Mechanism

- **The character.** `R_nu` acts on the offsets `c = x - y` of the quadrant-I half-lines
  through a surjective character `chi_1`, with `chi_1(L_h) = h1 - h2` and
  `chi_1(sigma) = -1`.
- **A nonzero coordinate.** The projection of `R_nu'` to shift amounts on quadrant-I lines is
  a nonzero ideal of `Z[t^(+-1)]`.
- **The contradiction.** A finite presentation would split `ker(chi_1)` ascendingly over a
  finitely generated subgroup (`fp-groups-without-free-subgroups-split-ascendingly-over-kernels`),
  because metabelian groups contain no free subgroup of rank 2. That confines this ideal to
  one-sided Laurent degrees, which is impossible.

In Bieri–Strebel terms, the relation module is not tame.

## Not claimed

- Nothing about other enumerations of `Z^2`.
- Nothing about finite presentation of the shell envelope `E_nu` itself, for which the gate
  and `A_1` are not known to be necessary.

DERIVATION
square-spiral-z2-near-shift-group-not-fp-proof
