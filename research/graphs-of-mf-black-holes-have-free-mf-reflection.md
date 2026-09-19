---
rg: 2
id: graphs-of-mf-black-holes-have-free-mf-reflection
kind: claim
title: A graph of full-radical groups has free MF reflection determined only by graph cycles
artifacts:
  - research/graphs-of-mf-black-holes-have-free-mf-reflection-proof.md
---

Let `Y` be a connected countable graph and let `G(Y)` be a countable graph of
groups over `Y`.  Assume every vertex group has full MF radical; no additional
hypothesis is needed on the edge groups beyond the given edge embeddings.
Let

```text
Pi=pi_1(G(Y)),
F_Y=pi_1(Y),
```

where `F_Y` is the free group on the edges outside a maximal tree.  Killing
all vertex groups defines a canonical surjection

```text
pi:Pi->F_Y.
```

Then

```text
Rad_MF(Pi)=ker(pi)=normalClosure_Pi(all vertex groups), (BG1)
R_MF(Pi)=F_Y,                                           (BG2)
Hom(Pi,M) ~= Hom(F_Y,M)                                 (BG3)
```

naturally for every MF group `M`.

Thus a tree of full-radical groups again has full MF radical, while every
cycle contributes exactly one free MF-visible generator and nothing else.

If `Y` is finite, the vertex groups are finitely presented, and the edge
groups are finitely generated, then `Pi` is finitely presented.  Taking every
vertex group to be the finitely presented Hilbert-hotel group produces, for
every finite connected graph, an explicit finitely presented group whose
entire MF reflection is the free group of rank `b_1(Y)` and whose MF radical
is exactly the normal closure of its vertex groups.
