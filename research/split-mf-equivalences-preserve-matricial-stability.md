---
rg: 2
id: split-mf-equivalences-preserve-matricial-stability
kind: claim
title: Split MF-equivalences preserve point-norm matricial stability
root: true
artifacts:
  - research/split-mf-equivalences-preserve-matricial-stability-proof.md
distinct_from:
  matricial-stability-identifies-radicals: that computes the MF radical once stability is known; this transports the stability property itself across a split quotient.
  hs-stability-descends-to-retracts: that gives one direction for Hilbert--Schmidt stability along a retract; this gives both directions for point-norm stability using exact equality of norm-corona representation functors.
  mf-equivalences-form-a-colimit-stable-localization: that develops the localization calculus and its colimit properties; this proves that a split equivalence also preserves point-norm matricial stability.
---

Let

```text
pi:G->Q,                  s:Q->G,          pi s=id_Q   (SCE1)
```

be a split epimorphism and an MF-equivalence of countable groups.  Then for
every matrix size sequence `d`, precomposition with `pi` is a bijection

```text
Hom(Q,U(Q_d)) -> Hom(G,U(Q_d)),                        (SCE2)
```

where `Q_d=product_n M_(d_n)(C)/directSum_n M_(d_n)(C)` is the norm matrix
corona.  Then

```text
G is point-norm matricially stable
 iff Q is point-norm matricially stable.               (SCE3)
```

The forward implication is retract stability.  Given an asymptotic
representation of `Q`, compose it with `pi`, correct on `G`, and restrict
the correcting homomorphisms along `s`.

For the reverse implication, let `phi_n:G->U(d_n)` be asymptotically
multiplicative.  Its corona homomorphism factors through `pi` by `(SCE2)`.
Consequently

```text
||phi_n(g)-phi_n(s pi(g))|| -> 0                       (SCE4)
```

for every fixed `g`.  The restriction `phi_n s` is an asymptotic
representation of `Q`; stability of `Q` corrects it to homomorphisms
`rho_n:Q->U(d_n)`.  Then `rho_n pi` are homomorphisms on the original matrix
spaces and `(SCE4)` makes them pointwise close to `phi_n`.

Thus stability is invariant under split quotients which erase no norm-corona
representation data.  The theorem uses no uniform modulus and does not
change or enlarge the finite-dimensional models.

To obtain `(SCE2)`, observe that the image of any homomorphism from `G` to
`U(Q_d)` is a countable MF group.  The Hom-bijection defining an
MF-equivalence factors the map through `Q`, and surjectivity of `pi` gives
uniqueness.
