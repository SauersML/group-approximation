---
rg: 2
id: sl3-finite-building-quotients-forget-arithmetic-labels
kind: claim
title: Finite quotients of the SL3 building do not automatically retain the dense arithmetic action labels
artifacts:
  - research/artifacts/sl3-building-quotient-label-audit-2026-08-21.md
distinct_from:
  native-hecke-graph-action-is-the-permanence-firewall: that isolates the consequences of soficity of the Hecke graph action; this proves why ordinary unlabelled building quotients do not establish that premise.
  codense-tau-coset-soficity-forces-permutation-instability: that constrains hypothetical action models analytically; this is the exact covering-space descent obstruction to constructing them from finite building quotients.
---

Let `X=G/K` be the type-zero vertex orbit for

```text
G=SL_3(Q_2),   K=SL_3(Z_2),
A=SL_3(Z[1/2]),   C=SL_3(Z).
```

For a torsion-free uniform lattice `Gamma<G`, an element `a in A` descends
from `X` to an automorphism of the finite quotient `Gamma\X` if and only if

```text
a Gamma a^(-1)=Gamma.                                    (FBL1)
```

Thus local convergence, large injectivity radius, or a random lift of the
unlabelled building does not by itself define the permutations labelled by
the fixed generators of `A`.  A fixed `KaK` Hecke relation does not repair
this: it records `gK -> gaK`, while the arithmetic action is `gK -> agK`
and has frame displacement `g^(-1)ag` at `gK`.

Consequently any building-quotient proof of soficity still needs coherent
simultaneous rounding of the deck cocycles for all labels and products in
each finite word window.  This is a construction fence, not a claim that
the action is nonsofic.
