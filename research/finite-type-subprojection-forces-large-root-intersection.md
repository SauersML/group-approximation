---
rg: 2
id: finite-type-subprojection-forces-large-root-intersection
kind: claim
title: A transported finite type inside one root block must meet the root subgroup at index at most the squared root dimension
artifacts:
  - research/finite-type-subprojection-large-intersection-proof.md
distinct_from:
  canonical-full-type-overlap-is-algebraic-corner-containment: that says full canonical overlap is equivalent to algebraic containment; this converts containment of a transported central type into an explicit subgroup-index and restriction-multiplicity obstruction.
  finite-subgroup-hecke-literals-cannot-block-escape: that traps a projection of the form qgq; this permits an arbitrary transported finite-subgroup central type and constrains its subgroup intersection with the root packet.
  bass-serre-algebraic-projections-are-stably-vertex-induced: that classifies stable projective classes over finite graphs of finite groups; this is an unstabilized canonical-trace obstruction valid in every ambient group.
---

Let `K,H` be finite subgroups of a group `Gamma`, let

```text
pi in Irr(K),       rho in Irr(H),
q=z_(K,pi),         p=g z_(H,rho) g^(-1),
A=gHg^(-1),         L=K intersect A.
```

Write `rho^g` for the transported representation of `A` and put

```text
m=<Res^K_L pi,Res^A_L rho^g>_L.                         (LRI1)
```

If

```text
0!=p<=q                                                  (LRI2)
```

as algebraic projections in `C[Gamma]`, then

```text
m=d_rho [K:L]/d_pi.                                     (LRI3)
```

In particular

```text
[K:L]<=d_pi^2,              d_pi divides d_rho [K:L].  (LRI4)
```

The equality case is rigid. If `[K:L]=d_pi^2`, then
`m=d_rho d_pi`, so every linear map between the two restriction spaces is
`L`-equivariant. Consequently both restrictions are scalar copies of the
same one-dimensional character of `L`.

Thus a context partition

```text
q=sum_a p_a
```

whose atoms are single transported central finite types has a compulsory
large-intersection property: for every `a`,

```text
[K:K intersect g_a H_a g_a^(-1)]<=d_pi^2.              (LRI5)
```

This is already sharp for the live hyperoctahedral packet
`K_D=(C_2)^D semidirect S_D` with its tautological `D`-dimensional root
type. For `D>=3`, an atom group meeting `K_D` only in the global central
sign has index `2^(D-1)D!>D^2` and is impossible. For `D>=4`, even an
intersection contained in the whole diagonal sign torus has index at least
`D!>D^2` and is impossible. Every single-type chord atom must retain
substantial permutation stabilizer.

More generally, if all new atom groups meet `K` inside a fixed selector
subgroup `Z<=K` and

```text
[K:Z]>d_pi^2,                                           (LRI6)
```

then no nonzero transported finite type from any of those groups can be
subordinate to `q`. In particular, making face groups intersect the root
packet only in a small common central sign cannot produce escaped context
atoms in a large root type.

The obstruction is specific to a single transported type. A coherent sum of
several double-coset/type terms can lie under `q` through additive
interference without any one summand being a projection under `q`. Hence
`(LRI4)` does not refute the signed-Hecke programme; it proves that a live
block-escaping chord with small root intersections must be genuinely
multipath rather than one finite-type arrow.
