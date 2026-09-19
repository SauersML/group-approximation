---
rg: 2
id: agent-first-hit-finite-fresh-tree-has-marked-matrix-model
kind: claim
title: Every finite fresh-copy packet and Reynolds HNN tree has an exact marked matrix model
distinct_from:
  canonical-types-extend-every-finite-bass-serre-actor: that extends an already canonical ultraproduct base through finite actors; this constructs a finite-dimensional marked model for a finite tree containing arbitrarily many fresh structural BCS copies.
  finite-packet-graph-atlases-have-a-regular-stationary-flow: that treats only finite vertex groups abstractly; this supplies compatible finite quotients of all fresh structural BCS vertex groups and keeps the common central mark equal to minus one.
  agent-first-hit-fresh-copy-reynolds-tree-is-contractive: that proves the intended active recurrence is contractive; this gives a defect-zero countermodel to every finite construction in the stated class.
---

**ESTABLISHED.**  Fix any finite presentation assembled from the following
pieces:

1. finitely many fresh structural BCS groups, with one involution for each
   shared variable, a common central involution `J`, and only the involution
   and within-context commutation relations;
2. finitely many finite role, selector, and address packets, commuting with
   the prescribed BCS variables and sharing the same central mark `J`;
3. finitely many amalgam or HNN covariance rows identifying marked finite
   subgroups, including the index-two Reynolds-pair transports used to send
   forbidden atoms to target characters; and
4. no additional relation among the edge intertwiners.

Then this presentation has an exact finite-dimensional unitary representation
with

```text
J=-I.                                                   (FMT1)
```

In particular every finite fresh-copy first-hit tree made only from these
operations retains an exact marked matrix model.  It therefore cannot imply a
dimension-independent normalized-Hilbert--Schmidt defect floor separating
`J` from the identity.

## Construction

For each structural BCS copy, impose extra commutations between all of its
variables.  This gives a finite elementary-abelian quotient whose negative
`J`-sector is the uniform sum over all global Boolean valuations.  Every
context assignment occurs there with the same multiplicity.  Combine this
quotient with the actual finite role/address packets, amalgamating their
central involutions.  The resulting finite marked quotient `F_v` of each
vertex block contains every finite source and target packet used by the HNN
rows.

Let

```text
lambda^-_(F_v)
```

denote the negative central corner of the regular representation of `F_v`.
The central involution acts as `-I`.  If a marked finite subgroup `H<=F_v`
contains `J`, then

```text
Res_H lambda^-_(F_v)
  isomorphic to [F_v:H] lambda^-_H.                    (FMT2)
```

Choose one integer `L` divisible by every `|F_v|` and take

```text
V_v=(L/|F_v|) lambda^-_(F_v).                          (FMT3)
```

For every marked edge group `H_e` incident to `v`,

```text
Res_(H_e) V_v
  isomorphic to (L/|H_e|) lambda^-_(H_e),              (FMT4)
```

independently of the endpoint.  Hence the two endpoint restrictions along
every amalgam or HNN row are unitarily equivalent.  Choose an intertwining
unitary for each non-tree edge and identify spaces along a maximal tree.
Because the presentation imposes no further relation among those
intertwiners, all choices can be made independently and give one exact finite
matrix representation satisfying `(FMT1)`.

The same argument applies when all pieces are presented as HNN loops on one
base vertex: the source and target subgroups have the same order and the two
restrictions of `(FMT3)` are equal marked-regular multiples, so an
intertwiner exists for every stable letter.

Every forbidden Reynolds character has positive multiplicity in this model.
Its HNN target has exactly the same multiplicity.  This is the regular-trace
compensation in finite-dimensional form, not merely an obstruction visible
in the left regular trace of the final group.

In particular, the phrase "put the fresh tuple on the union of target atoms"
is not supplied by adjoining fresh group generators and finite-subgroup HNN
rows.  Those generators act on the whole representation.  Making their
nontrivial action conditional on the target projection is itself an extra
corner-localization relation.  If that relation is absent, the marked model
above applies; if it is present and is not finite-subgroup covariance, it is
already the payload-sensitive two-cell excluded in item 4.

## Exact scope

The perfect non-CE tracial BCS model may also extend through the same tree by
making every forbidden source and its destination vanish.  That does not help
finite-dimensional soundness: the marked model above is a second exact model
of the same ordinary presentation in which all finite packet characters occur
with their stationary regular multiplicities.

The theorem stops applying as soon as one adds a genuine two-cell constraining
several stable-letter intertwiners, or a payload-sensitive relation not
reducible to finite-subgroup covariance.  Such a relation would have to
destroy the marked-regular stationary model while remaining vacuous on the
perfect BCS trace.  Constructing precisely that extra relation is the missing
compiler.

DERIVATION
agent-first-hit-finite-fresh-tree-has-marked-matrix-model via agent-first-hit-marked-regular-flow-proof
