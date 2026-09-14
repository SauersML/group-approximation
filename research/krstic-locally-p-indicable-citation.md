---
rg: 2
id: krstic-locally-p-indicable-citation
kind: route
title: Import Krstic's p-nonsingular systems theorem for one equation, and prove the extension and screening consequences
target: krstic-p-nonsingular-equations-inject-locally-p-indicable-groups
requires: []
artifacts:
  - research/artifacts/hl-kl-torsion-pins-2026-09-13.md
---

**Imported, at second hand.** Klyachko--Mikheenko, arXiv:2309.09096,
`main.tex` l.271--274: "Theorem [Kr85]. Let p be a prime. A finite p-nonsingular
system of equations over a locally p-indicable group is solvable." The
definitions it uses are pinned in section 2 of the artifact:
- solvability of a system over `G` is equivalent to `G cap <<W>> = {1}` in
  `G * F(X)` (l.126--133);
- p-nonsingularity means the rows of exponent sums mod `p` are linearly
  independent over `Z_p` (l.170--177);
- local `p`-indicability (l.251--254).
Krstic's 1985 paper was not read.

**The one-equation case.** `w = 1` is a system of one equation in one variable
`t`, and its exponent-sum row is `(m)`. The row is independent over `Z_p` iff
`p` does not divide `m`. By Krstic the system is solvable, so
`G cap <<w>> = {1}` in `G * <t>`, which is injectivity.

**Consequence 1 (extensions).** Let `S <= G` be nontrivial and finitely
generated.
- If `S <= H`, then `S` maps onto `Z/p` because `H` is locally `p`-indicable.
- Otherwise `SH/H` is a nontrivial finitely generated subgroup of `G/H`, so it
  maps onto `Z/p`, and `S` maps onto `SH/H`.

The three examples:
- **Finite `p`-groups.** A nontrivial `p`-group `P` has a proper normal
  subgroup of index `p`, so `P` maps onto `Z/p`. Subgroups of `p`-groups are
  `p`-groups.
- **Residually finite-`p` groups.** A nontrivial finitely generated `S` has an
  element surviving in some finite `p`-quotient `G/N`. Then `SN/N` is a
  nontrivial `p`-group and maps onto `Z/p`.
- **Locally indicable by finite `p`-group.** A locally indicable group maps its
  nontrivial finitely generated subgroups onto `Z`, hence onto `Z/p`. Apply
  consequence 1 with a finite `p`-group quotient.

**Consequence 2 (screen).** By `kl-failure-localizes-to-the-coefficient-subgroup`,
a violation over `G` is already a violation over the finitely generated
coefficient subgroup `A`. If `A` were locally `p`-indicable for some `p` not
dividing `m`, the one-equation case would inject `A`, a contradiction.

That node was cited here, not added to `requires`, because the screen is a
remark and the target claim is the import.
