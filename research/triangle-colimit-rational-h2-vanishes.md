---
rg: 2
id: triangle-colimit-rational-h2-vanishes
kind: claim
title: Every colimit of a developable triangle of finite groups has vanishing rational second cohomology
distinct_from:
  compact-hyperbolic-km-lattices-fail-lp: that is the open LP-failure fork, whose attempts record the real second cohomology of the Kac--Moody lattices as undetermined and tilt toward nonvanishing; this decides that cohomology to be zero, killing the trivial-coefficient clause of Ioana--Spaas--Wiersma Corollary E at every triangle colimit.
  km-lattices-admit-no-cocompact-npc-model: that shows the triangle development is never CAT(0), so contractibility is unavailable; this shows contractibility was never needed for degree two, because simple connectivity of the development already forces the vanishing.
  titz-witzel-lattices-fail-lp: that uses a free cocompact action on a contractible building, where Brown's identification applies verbatim; this treats proper cocompact actions on a simply connected but possibly non-contractible complex, where only the low-degree part of the Cartan--Leray spectral sequence survives.
---

**THEOREM (established; proof in
`triangle-colimit-rational-h2-vanishes-proof`).**  Let `Lambda` act
cellularly, without inversions, with finite stabilizers and finitely
many orbits of cells on a simply connected CW complex `X` such that the
quotient `X/Lambda` satisfies `H^1(X/Lambda;Q)=H^2(X/Lambda;Q)=0`.  Then

```text
H^1(Lambda;Q)=0,        H^2(Lambda;Q)=0,                    (RH1)
```

and for EVERY `Lambda`-module `M` the inflation map is injective with
explicit image

```text
H^2(Lambda;M)  =  ker( H^2_Lambda(X;M) --> H^2(X;M) ),      (RH2)
```

the kernel of the map forgetting equivariance.  If moreover `M` is a
`Q`-vector space, the equivariant group is the cokernel of the cellular
coboundary of the quotient with stabilizer-fixed coefficients.

**Instance: triangles of finite groups.**  Let

```text
P_0 <= P_1,P_2,P_3 <= P_12,P_13,P_23
```

be a developable triangle of finite groups with colimit `Lambda`, and let
`X` be its development.  `X` is simply connected (Bridson--Haefliger,
*Metric spaces of non-positive curvature*, III.C.3.13: the development
with respect to the canonical morphism to the fundamental group of the
complex of groups is simply connected; for a simplex the fundamental
group is the colimit), `Lambda` acts with finite stabilizers (conjugates
of the `P_J`), without inversions, and with quotient one contractible
triangle.  Hence

```text
H^2(Lambda;Q)=0,   H^2(Lambda;R)=0,
H^2(Lambda;M) = ker( M^(P_0)/(M^(P_1)+M^(P_2)+M^(P_3)) --> H^2(X;M) )
                                  for every Q-vector-space module M.  (RH3)
```

**Kac--Moody consequence.**  The simple Kazhdan Kac--Moody lattices of
`simple-kazhdan-kac-moody-lattices-exist` are colimits of their
Abramenko--Mühlherr triangle of finite rank-`<=2` Levi subgroups (the
amalgam of [AM97] recorded in
`triangle-colimit-llp-reduces-to-relator-local-splitting`; B. Rémy,
*Kac-Moody groups as discrete groups*, arXiv:math/0402300, Theorem 5,
read at source: `2`-spherical and `q>3` gives finite presentability by
that amalgam).  Therefore

```text
H^2(Lambda_(2,4,6)(q);R)=0.                                 (RH4)
```

The trivial-coefficient clause of Ioana--Spaas--Wiersma Corollary E
(`H^2(Gamma,R)!=0` forces LP failure for Kazhdan `Gamma`) therefore
CANNOT fire at any Kac--Moody lattice, nor at any other triangle colimit.
The earlier "tilt" toward `H^2(Lambda;R)!=0` recorded in
`compact-hyperbolic-km-lattices-fail-lp` is withdrawn.  What survives of
Corollary E is only its `L^0(Y,R)`-coefficient clause, and `(RH3)`
rewrites that as: a `T`-invariant measurable function on an ergodic
p.m.p. `Lambda`-space which is not a sum of `P_1`-, `P_2`-, `P_3`-invariant
functions and whose equivariant extension to the development is a
coboundary there.  The integral group-ring clause (Corollary D) is
treated separately in `km-group-ring-h2-is-development-end-cohomology`.

**Why contractibility was a red herring.**  The vanishing repaired on
2026-08-21 had assumed a contractible cocompact model.  Degree two needs
only `H^1(X)=0`: the Cartan--Leray spectral sequence
`E_2^(p,q)=H^p(Lambda;H^q(X;M))` has `E_2^(*,1)=0`, so `E_2^(2,0)`
receives no differential and injects into `H^2_Lambda(X;M)`.  The
non-contractibility of `X` (equivalently `H_2(X)!=0`) enters only through
the target `H^2(X;M)` in `(RH2)`, never through the injectivity.
