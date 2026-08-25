---
rg: 2
id: non-cohyperlinear-irs-exists
kind: claim
title: A non-co-hyperlinear invariant random subgroup exists on a nonabelian free group
distinct_from:
  non-hyperlinear-group: a non-co-hyperlinear IRS need not be a point mass at a normal subgroup, so this does not produce a group whose regular trace is non-embeddable.
  diracization-gap-equals-nonhyperlinear-group: that identifies the additional normal-Dirac gap needed to obtain a nonhyperlinear quotient group; this claim stops at a genuinely random subgroup.
artifacts:
  - research/artifacts/three-paper-cairn-ingestion-2026-08-20.md
---

Every nonabelian free group admits an invariant random subgroup `H` whose IRS
trace

```text
tau_H(g) = Pr[g in H]
```

is not amenable.  Equivalently, the GNS von Neumann algebra denoted
`L(F/H)` by Manzoor is not Connes embeddable.

The transfer from an IRS-strategy gap uses the negative central sector to
obtain a nonamenable trace on the game's free-product group, then pulls that
trace back to a free group.  Passing between nonabelian finite-rank free groups
preserves the conclusion.

This is an action/character endpoint, not Cairn's goal
[[non-hyperlinear-group]].  Taking a normal core or independent intersections
can erase the non-embeddability information; [[diracization-gap-equals-nonhyperlinear-group]]
records the exact missing normal-Dirac step.

There is one stronger finite-orbit endpoint.  By
[[atomic-noncohyperlinear-irs-forces-nonhyperlinear]], if an ergodic choice of
the IRS has even one atom, its finite conjugacy orbit is a finite-index
induction of the regular character of `N_Gamma(H)/H`; non-CE then forces that
quotient group to be non-hyperlinear.  Thus every Manzoor witness is either
nonatomic or already terminal.  The cited existence theorem does not decide
which side occurs.

Moreover `ergodic-nonce-irs-fg-support-is-terminal` shows that finite
generation of the random subgroup on any positive-measure part of an
ergodic witness is already terminal.  In the genuinely unresolved branch,
the IRS is therefore nonatomic and almost surely supported on infinitely
generated subgroups; resolving all finite-quotient images need not atomize
such a law.
