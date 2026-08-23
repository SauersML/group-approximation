---
rg: 2
id: fixed-clifford-multiplier-is-nonsplit-root-double-cover
kind: claim
title: The fixed Clifford multiplier is a central double cover nonsplit on both dyadic root cycles
distinct_from:
  fixed-clifford-projective-dyadic-tower: that identifies the full-inertia projective category and its conductor shift; this computes the multiplier's central extension and its restrictions to the two root cyclic subgroups.
  fixed-clifford-sectors-have-zero-adjacent-opposite-overlap: that compares the newest-layer characters under the opposite depth shift; this proves a cyclic spectral recursion internal to one fixed-character multiplier.
  iwahori-dual-inclusion-graph-is-fusion-not-the-bruhat-tits-tree: that excludes a spatial-tree Kesten estimate; this excludes a uniform estimate based only on either cyclic root marginal.
---

For `a>=2`, retain the notation

```text
G_a=SL_2(Z/2^a),
L_a=ker(G_a->G_(a-1)),
chi_a(1+2^(a-1)X(A,B,C))=(-1)^(A+B+C).              (FCM1)
```

Because `chi_a` is `G_a`-invariant, `ker(chi_a)` is normal and

```text
E_a=G_a/ker(chi_a)                                   (FCM2)
```

fits into a central extension

```text
1 -> <z> = C_2 -> E_a -> G_(a-1) -> 1.               (FCM3)
```

For any section `s:G_(a-1)->G_a`, the multiplier in
`fixed-clifford-projective-dyadic-tower` is represented by

```text
omega_a(g,h)=chi_a(s(g)s(h)s(gh)^(-1)).              (FCM4)
```

Consequently

```text
Rep_(omega_a)(G_(a-1)) = Rep(E_a | z acts as -1),    (FCM5)
```

up to the harmless inverse-multiplier convention.

This double cover is non-split, already on each standard root cycle.  If

```text
u=[[1,1],[0,1]],       l=[[1,0],[1,1]],
```

then their images in `E_a` obey

```text
u^(2^(a-1))=z,         l^(2^(a-1))=z.                (FCM6)
```

Thus the inverse image of either order-`2^(a-1)` root subgroup of
`G_(a-1)` is cyclic of order `2^a`; the restricted extension is

```text
1 -> C_2 -> C_(2^a) -> C_(2^(a-1)) -> 1,             (FCM7)
```

not the split extension. In particular `[omega_a]` is nonzero in
`H^2(G_(a-1),{+1,-1})`.

Every representation in `(FCM5)` therefore has the exact root spectral
constraint

```text
U^(2^(a-1))=-I.                                      (FCM8)
```

Its root eigenvalues are odd `2^a`-th roots of unity. Squaring maps this
set onto the odd `2^(a-1)`-th roots, with equal two-point fibers, and

```text
(U^2)^(2^(a-2))=-I.                                  (FCM9)
```

On the negative-central regular block of `E_a`, all odd root characters
occur with equal multiplicity. Hence the cyclic root marginal has an exact
zero-loss refinement/coarsening recursion across depth: distribute mass
uniformly over the two square roots at the next level and squaring returns
the preceding marginal exactly.

Therefore no uniform upper/opposite boundary can follow from either root
spectrum, its conductor, or its one-variable power relations alone. A
surviving expansion theorem must use joint information coupling the two
root lifts (equivalently, genuinely noncommutative words or the full cocycle)
and must also account for the size-three inertia sectors forced by
`fixed-clifford-sectors-have-zero-adjacent-opposite-overlap`.

This is only a cyclic-marginal firewall. It does not construct a Folner
profile for the full upper/opposite representation overlay.
