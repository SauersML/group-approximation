---
rg: 2
id: integral-group-ring-congruence-groups-are-torsion-free-mf
kind: claim
title: Congruence groups over an integral group ring are torsion-free and MF for every input group
distinct_from:
  perfect-torsion-free-mf-group-has-no-fd-representations: that is one explicit group refuting an inference from exact finite-dimensional collapse; this rules out a whole family of proposed constructions, for every input group at once, and says nothing about finite-dimensional radicals.
  torsion-free-central-cover-forces-abelian-finite-subgroups: that kills central-cover procedures by a finite-subgroup obstruction; this kills group-ring congruence procedures by proving their outputs are always MF.
  full-mf-radical-seed-has-no-torsion-free-quotient: that rules out homomorphic-image transfers by exhibiting an input with no nontrivial torsion-free quotient; this rules out a construction whose output is torsion-free but always MF, so the failure is at the other end.
artifacts:
  - research/artifacts/torsion-free-cover-perfect-and-congruence-obstructions-2026-09-08.md
---

**ESTABLISHED.**  For every countable group `G` and every `d >= 1`, put

```text
Gamma_d(G) = { U in GL_d(Z[G]) : U = I mod 3 }.                   (CG1)
```

Then `Gamma_d(G)` is **torsion-free**, every finitely generated subgroup of
it is **residually finite**, and therefore `Gamma_d(G)` and all of its
subgroups are **operator MF**.

The input group is arbitrary: `G` may be non-MF, may have full MF radical,
may be the Leavitt or Jacobson unit group.  None of that reaches the
congruence group.

**What this excludes.**  Any proposed torsion-free transfer whose output is
a subgroup of some `Gamma_d(G)` fails, whatever the input.  The
`3`-adic filtration that makes the output torsion-free is the same
filtration that makes it locally residually finite, so the two desired
properties are in direct conflict here.  This is an obstruction to a family
of constructions, not to the transfer itself:
`free-abelianized-cover-reflects-mf` is untouched.

DERIVATION
group-ring-congruence-torsion-free-mf-proof
