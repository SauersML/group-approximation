---
rg: 2
id: cycle-closure-cannot-remain-in-the-join-tree-group
kind: claim
title: A no-CE BCS cycle atlas cannot be completed inside its join-tree group
artifacts:
  - research/artifacts/signed-hecke-common-type-normalization-2026-08-20.md
distinct_from:
  root-block-piecewise-transport-cannot-host-nonce-bcs: that rules out an atlas confined to the finite root matrix block; this rules out a completed atlas anywhere in the whole residually finite join-tree group corner.
  first-cycle-signed-hecke-chord: that permits enlarging the group and asks for the first exact cyclic operation; this proves that merely finding more algebraic unitaries in the already constructed acyclic ambient group cannot finish the no-CE source.
---

For the join-tree construction `(JTA1)`,

```text
Gamma_T=K_D times F_D^(1) times ... times F_D^(m)         (CJG1)
```

is residually finite and hence hyperlinear.  If the omitted BCS overlap
equalities could all be closed by replacing or regauging context projections
inside the unchanged corner

```text
q_D C[Gamma_T] q_D,                                      (CJG2)
```

then the completed compatible atlas would give a unital map from the no-CE
BCS algebra into `(CJG2)`.  The normalized canonical corner trace would pull
back to a Connes-embeddable tracial state, a contradiction.

Consequently at least one cyclic step must enlarge the ambient group in a way
whose hyperlinearity is not already guaranteed.  Finite endpoint criteria
such as `(WIF3)` can certify or exclude a proposed local regauge, but they
cannot by themselves complete the no-CE atlas inside the existing free-phase
group.
