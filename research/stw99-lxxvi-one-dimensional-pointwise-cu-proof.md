---
rg: 2
id: stw99-lxxvi-one-dimensional-pointwise-cu-proof
kind: route
title: Apply the natural idealwise K1-free formula on the whole one-dimensional base
target: stw99-lxxvi-one-dimensional-formation-preserves-cu-regularity
requires: []
artifacts:
  - research/artifacts/stw99-lxxvi-fourth-depth-audit-2026-08-30.md
---

Antoine--Perera--Santiago, Theorem 3.4 in
[*Pullbacks, C(X)-algebras, and their Cuntz
semigroup*](https://arxiv.org/abs/1101.4776), states that if `Y` is
second-countable, locally compact, Hausdorff, and of covering dimension at
most one, and a separable coefficient `F` has stable rank one and satisfies

```text
K_1(J)=0 for every closed two-sided ideal J of F,             (2)
```

then fiber evaluation is an isomorphism in the category `Cu`:

```text
alpha_F:Cu(C_0(Y,F)) ~= Lsc(Y,Cu(F)).                        (3)
```

Apply (3) to `F=B` and to `F=E=B tensor_min Z`.  The canonical tensor
identification

```text
C_0(X,B) tensor_min Z ~= C_0(X,B tensor_min Z)=C_0(X,E)      (4)
```

intertwines evaluation at each `x in X` with the first-factor map `B->E`.
Because the isomorphisms in (3) are evaluation maps, naturality makes the
diagram

```text
Cu(C_0(X,B))  -------------------->  Cu(C_0(X,E))
     |                                      |
     | alpha_B                              | alpha_E
     v                                      v
Lsc(X,Cu(B))  --Lsc(X,Cu(B->E))-->  Lsc(X,Cu(E))
```

commute.  The bottom arrow is an isomorphism whenever `Cu(B)->Cu(E)` is one:
its inverse is pointwise application of the inverse `Cu`-morphism.  Thus the
top arrow is an isomorphism, proving the reusable theorem.

For the corollary, let `B=D` be simple, separable, stably finite, and pure,
with `K_1(D)=0`.  Lin's stable-rank theorem, quoted as STW Theorem 21, gives
stable rank one for `D`.  The algebra `E=D tensor_min Z` is again simple,
separable, stably finite, and pure, so it too has stable rank one.  Simplicity
reduces (2) to `K_1(D)=K_1(E)=0`; the latter equality follows because the
first-factor inclusion is a KK-equivalence.  STW Proposition 23 says that
`Cu(D)->Cu(E)` is an isomorphism.  All hypotheses of the reusable theorem are
therefore satisfied.

It remains only to verify the claimed purity for a noncompact base.  The
one-point compactification `X^+` is compact metrizable.  Seth--Vilalta,
Corollary 5.9 in
[*Continuous functions over a pure C*-algebra*](https://arxiv.org/abs/2602.14809),
makes `C(X^+,D)` pure.  The algebra `C_0(X,D)` is its ideal of functions
vanishing at infinity, and pureness passes to ideals by the
Perera--Thiel--Vilalta purity-extension theorem.  Hence `C_0(X,D)` is pure.

The idealwise `K_1` restriction is a trust boundary of the pointwise proof,
not a restriction on the topology beyond dimension one.
Antoine--Dadarlat--Perera--Santiago remove it for an interval and retain a
separate compact clutching summand for a circle.  Their Remark 3.9 gives a
circle with an attached interval where pointwise comparison misses a nonzero
`K_1` clutching class.  No pointwise formula is asserted after deleting (2).
