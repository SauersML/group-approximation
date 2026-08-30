---
rg: 2
id: stw99-lxxvi-finite-tree-leaf-induction-proof
kind: route
title: Attach one unprescribed leaf endpoint at a time
target: stw99-lxxvi-finite-tree-formation-preserves-cu-regularity
requires: []
artifacts:
  - research/artifacts/stw99-lxxvi-finite-tree-noncompact-audit-2026-08-30.md
---

Stabilize the coefficient.  The base case is
Antoine--Dadarlat--Perera--Santiago, Theorem 2.6:

```text
Cu(C([0,1],D)) ~= Lsc([0,1],Cu(D))
```

for every simple separable stable-rank-one `D), with no `K_1)
restriction.

For the induction step, write a tree with a leaf edge as

```text
T=T' union_v [0,1],
C(T,D)=C(T',D) pullback_D C([0,1],D).
```

The interval evaluation map is an order embedding, so the pullback
surjectivity theorem gives a surjection

```text
Cu(C(T,D))
 -> Cu(C(T',D)) pullback_Cu(D) Cu(C([0,1],D)).            (1)
```

To see that (1) reflects order, follow the standard pullback comparison
proof.  Stable rank one produces a unitary in the hereditary gluing fiber
which aligns the two comparison vectors at `v`.  Propagate its action along
the support component of the new edge.  If the component reaches `1`, that
endpoint is unprescribed and no compatibility condition remains.  If it ends
earlier, propagate on a compact initial subinterval and splice the comparison
vectors where they tend to zero.  The latter changes the comparison estimate
by an arbitrarily small norm, even when the propagated unitary has nonzero
`K_1)-class.  Proposition 2.2 and Remark 2.3 of
Antoine--Dadarlat--Perera--Santiago provide the propagation on each compact
nonvanishing subinterval.

The partition-of-unity estimate from the pullback order-embedding proof now
gives the desired global comparison.  Thus (1) is an order isomorphism.
Induction on the number of leaf edges and the elementary identity

```text
Lsc(T',S) pullback_S Lsc([0,1],S) ~= Lsc(T,S)
```

prove the formula.  All maps used are evaluations, so the formula is natural
for coefficient star homomorphisms.  Applying it to
`D->D tensor_min Z` proves the Cu-regularity corollary.
