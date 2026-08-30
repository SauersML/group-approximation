---
rg: 2
id: profile-itinerary-meet-central-compression-proof
kind: route
title: Intersect the full profile itinerary and isolate its minimal central readable orbit
target: profile-itinerary-meet-extracts-finite-readable-summand
requires: []
---

Let `T` be the finite orbit of `p_0` and

```text
H={h in Q_G:pi(h)p_0pi(h)^*=p_0}.
```

Then `[Q_G:H]=|T|`. A nonzero projection cannot lie below two distinct
atoms of `D_0`, so the profile `r(gH)` containing
`pi(g)p_0pi(g)^*` is well defined on the left coset space `Q_G/H`.
For every `g`, profile purity gives

```text
p_0 <= pi(g)^* E_(r(gH)) pi(g).                         (PIM1)
```

All projections on the right belong to `D_infinity`. Their meet `q_0`
in `(PIC1)` therefore belongs to `D_infinity`, and `(PIM1)` gives
`p_0<=q_0`, so `q_0!=0`. The term with `g=1` gives
`q_0<=E_(r(H))`. If `h in H`, right multiplication
`g |-> gh^(-1)` preserves every left coset `gH`; reindexing the meet
gives

```text
pi(h)q_0pi(h)^*=q_0.                                   (PIM2)
```

Moreover, the factor of the meet indexed by `g=x` gives

```text
pi(x)q_0pi(x)^* <= E_(r(xH)).                           (PIM3)
```

Thus `q_0` has a finite profile-pure orbit, proving 1 implies 2 even when
the original projection was extrinsic to the generated game algebra.

For each `k in Q_G`, take `g=k^(-1)` in the defining meet. Then `q_0`
lies below one atom of `pi(k)D_0pi(k)^*`. Hence every element of every
translated readable algebra acts as a scalar on `q_0`. Since these
algebras generate `D_infinity`,

```text
q_0 in Z(D_infinity),       q_0 D_infinity q_0=Cq_0.   (PIM4)
```

Thus `q_0` is a minimal central projection of `D_infinity`. Every
conjugate has the same property, so distinct points of its finite orbit
`S` are orthogonal. Put

```text
z=sum_(q in S) q.                                       (PIM5)
```

Then `z in Z(D_infinity)` and `Q_G` fixes `z`. It therefore commutes
with `D_0` and with `pi(Q_G)), so `z in Z(N)`. For
`x in D_infinity`, each `xq` is scalar on `q`, while every orbit
projection belongs to `D_infinity z`. Consequently

```text
D_infinity z=direct_sum_(q in S) Cq,                    (PIM6)
```

which is finite-dimensional and abelian.

Conversely, suppose `0!=z in Z(N)` and `D_infinity z` is
finite-dimensional abelian. Choose one of its nonzero atoms. The
`Q_G` action preserves `z` and permutes finitely many atoms, and because
`D_0z` is a subalgebra, every orbit atom lies below a unique atom of
`D_0`. This proves 3 implies 2 and completes the same-model equivalence.

For a perfect model, central compression by `z` preserves all operator
relations and zero losing projections. Decompose `zN` over its center and
choose a factor component. The image of the finite-dimensional abelian
algebra `(PIM6)` remains finite dimensional and abelian, and the component
remains perfect. Conversely an atom of a finite abelian readable algebra
supplies condition 2. Finally, a Connes-embeddable perfect component would
produce finite-dimensional strategies with loss tending to zero, contrary
to `omega*(G)<1`; hence every perfect gap component is
non-Connes-embeddable.
