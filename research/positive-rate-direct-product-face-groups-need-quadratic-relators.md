---
rg: 2
id: positive-rate-direct-product-face-groups-need-quadratic-relators
kind: claim
title: A fixed packet times a positive-rate binary code needs quadratically many relators
distinct_from:
  positive-rate-tanner-tests-have-contextual-models: that builds exact contextual representations; this rules out the desired abstract direct-product presentation by group homology.
  fixed-k-code-product-gap-is-a-twisted-intertwiner-test: that computes the spectral condition assuming the direct product exists; this refutes its bounded-occurrence positive-rate presentation.
---

# A fixed packet times a positive-rate binary code needs quadratically many relators

ESTABLISHED.

Let `K` be any fixed finite group and put `G_r=K x (C_2)^r`. Every finite
presentation of `G_r` with `g` generators and `s` relators satisfies

```text
s >= g - b_1(G_r;F_2) + b_2(G_r;F_2)
  >= r(r+1)/2 - O_K(r) + g-r.                    (H2)
```

In particular, if `g=O(r)`, then `s=Omega(r^2)`.

Let `X` be the presentation two-complex. The Hopf exact sequence makes
`H_2(X;F_2) -> H_2(G_r;F_2)` surjective. Cellular homology, with one vertex,
gives `dim H_2(X;F_2)=s-g+b_1(G_r;F_2)`. The Kunneth summand
`H_2((C_2)^r;F_2)` already has dimension `r(r+1)/2`, the number of degree-two
monomials in the mod-two homology of an elementary abelian two-group. This
proves `(H2)`.

Now take homogeneous LCS faces of width at most `q`, on `g` variables, with
every variable occurring in at most `D` faces. Expanding the presentation
gives one square relation per variable and at most `1+binom(q,2)` relations
per face. Hence it has only `O_{D,q}(g)` relators. If its universal group were
exactly

```text
K x (C_2)^r,     r >= rho g
```

for fixed positive `rho`, `(H2)` would demand `Omega(g^2)` relators, a
contradiction for all sufficiently large `g`.

Therefore bounded-width, bounded-occurrence, positive-rate homogeneous LCS
faces cannot present the proposed exact direct product, for any fixed
nonabelian packet `K`. Auxiliary face variables do not help when their total
number remains `O(r)`.

This is stronger than the class-two contextual strategy: it rules out the
desired abstract group before approximate representations are considered. A
survivor must use a non-direct extension, lose positive rate, use superlinear
many bounded faces, or add a non-LCS global actor whose finitely many
relations generate the missing quadratic homology constraints by conjugacy.

The established private Weyl sampler deliberately lies outside this no-go:
it uses `g=Theta(r^2)` occurrence variables after quadratic repetition.  In
that low-rate regime the `Omega(r^2)` homology demand is only linear in `g`,
so the counting argument does not rule out an exact direct-product
completion.  The theorem kills the proposed positive-rate shortcut, not the
current quadratic-repetition program.
