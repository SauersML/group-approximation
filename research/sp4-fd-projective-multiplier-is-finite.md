---
rg: 2
id: sp4-fd-projective-multiplier-is-finite
kind: claim
title: Only finitely many scalar classes of Sp4(Z) are realizable by finite-dimensional projective representations
distinct_from:
  deligne-triple-cover-fd-central-invisibility: that kills one central mark (the mod-three Deligne cover) in exact matrices; this bounds the ENTIRE subgroup of finite-dimensionally realizable scalar classes at once, even orders, odd orders and torsion off the circle together.
  isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals: that computes the Levi-invariant scalar H^2 of the two parabolic RADICALS; this bounds the realizable classes of the full lattice Sp_4(Z), which is what Ioana--Spaas--Wiersma Theorem A actually consumes.
  sp4-metaplectic-class-pointwise-coboundary-limit: that is a topological statement (coboundaries are pointwise closed) true for every group; this is an arithmetic finiteness specific to Sp_4(Z).
---

Let `Gamma = Sp_4(Z)` and let

```text
R := { [c] in H^2(Gamma,T) : c is the exact 2-cocycle of some
       projective unitary representation pi: Gamma -> U(d), d < infinity }.
```

**THEOREM.**  `R` is a FINITE subgroup of `H^2(Gamma,T)`.  Quantitatively:
writing `H_2(Gamma,Z) = Z + F` with `F` finite (rank one; see the proof
route) and `t = |F|`,

```text
2t . R = 0   and   |R| <= 2t^2,                               (FM1)
```

and `R` meets the identity component of `H^2(Gamma,T) = T x Hom(F,T)`
(the Deligne--Maslov circle) only in classes of order at most `2` —
the trivial class and at most one metaplectic-type class.

**Why this is the right object.**  Ioana--Spaas--Wiersma Theorem A
(arXiv:2006.01874, p. 2, source-verified 2026-08-21) needs 2-cocycles of
the WHOLE group, each realized exactly by a finite-dimensional projective
representation, converging pointwise to `1`, with restrictions to some
subgroup staying non-coboundaries.  Every class such a datum can use lies
in `R`.  On their group `Z^2 x| SL_2(Z)` the analogous set is infinite
(the classes of `exp(2 pi i (xt-yz)/k)` pulled back from
`(Z/k)^2 x| SL_2(Z/k)`, their Section 3.2, p. 11); the theorem says the
symplectic lattice has no such supply: the mod-`N` Weil/theta data of the
congruence tower can pull back to at most the metaplectic `Z/2` plus a
bounded torsion group.  This matches the metaplectic-kernel computation
quoted by Stover (arXiv:2407.07680, discussion after Theorem 3.2,
source-verified 2026-08-21): by Prasad--Rapinchuk the absolute metaplectic
kernel of a group over a totally real field is `mu(k)^ = Z/2`.

Consumed by `isw-theorem-a-has-no-data-on-sp4-lattice`, which turns this
finiteness into the Lambda-uniform death of the ISW Theorem A mechanism
at `Sp_4(Z)`.
