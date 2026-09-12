---
rg: 2
id: one-free-reflection-contains-all-finite-free-reflections-proof
kind: route
title: Restrict the regular base to free subgroups and iterate a proper free self-embedding
target: one-free-reflection-contains-all-finite-free-reflections
requires:
  - leavitt-unit-internal-free-reflections
---

Write `F=F_2`.  Every finite-rank free group `F_r`, `r>=2`, occurs as a
subgroup of `F`; for example, a subgroup of index `r-1` has rank `r` by the
Nielsen--Schreier formula.  Inside

```text
W=U^(F) semidirectProduct F,
```

restrict the actor to such a subgroup `Q~=F_r` and restrict the base to the
coordinates indexed by `Q`.  This gives the internal subgroup

```text
U^(Q) semidirectProduct Q<=W.
```

The free-reflection theorem applies to this subgroup and gives `(UFR1)`,
finite generation, and single normal generation of the radical.  Universal
MF reflection is invariant under group isomorphism.  Since free groups of
distinct finite ranks are nonisomorphic, the corresponding internal
subgroups are pairwise nonisomorphic.

For the self-embedding, write `F=<a,b>` and define

```text
phi(a)=a,                 phi(b)=b a b^(-1).
```

The two images do not commute, so the subgroup they generate is a noncyclic
two-generated subgroup of a free group and therefore has rank two.  The
displayed pair is a minimal generating pair of that rank-two free subgroup,
so the Nielsen basis theorem makes it a free basis; equivalently, compose the
surjection onto this subgroup with an isomorphism back to `F_2` and use that
finitely generated free groups are Hopfian.  Hence `phi` is injective.  It is
not surjective: both images have `b`-exponent sum zero, so their subgroup does
not contain `b`.

Define `Phi` on the regular wreath product by

```text
Phi(g)=phi(g)                                      (g in F),
Phi((u_h)_(h in F))=(v_k)_(k in F),
v_(phi(h))=u_h,       v_k=1 if k is not in phi(F).       (UFR4)
```

The reindexing in `(UFR4)` is injective and intertwines the regular shift,
so it combines with `phi` to an injective endomorphism of `W`.  Its actor
image is the proper subgroup `phi(F)`, hence `Phi` is not surjective.  Since
`Phi` identifies `W` with its image, every inclusion

```text
Phi^(n+1)(W)<Phi^n(W)
```

is strict.  Quotienting by the base sends `(UFR4)` to `phi`, which proves the
reflection statement `(UFR3)`.
