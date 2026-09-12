---
rg: 2
id: infinite-chromatic-commutator-code-kills-mf-mark
kind: claim
title: A bounded-area infinite-chromatic commutator code kills its MF mark
distinct_from:
  bounded-area-high-chromatic-conjugacy-collapse: that uses order-three vertices, order-two edge products and normalized Hilbert--Schmidt packing to obstruct hyperlinearity; this uses diagonal versus off-diagonal commutators and operator-norm compactness to kill a mark in every norm matrix corona.
  finite-palette-packet-challenge-collapse: that assumes a finite palette of packet challenges with a dimension-dependent capacity bound; this obtains the collision from one infinite-chromatic graph and uniformly bounded relator area.
artifacts:
  - research/artifacts/property-t-free-atomic-leavitt-amr-2026-08-24.md
---

Let `Gamma=<S|R>` be finitely presented, let `z` be a word, and let
`G=(V,E)` be a graph with infinite chromatic number.  Suppose there are words

```text
c_v, h_v, a_v,                         v in V,
```

and constants `A_Delta,A_0<infinity` such that

```text
Area_R([c_v,h_v](a_v z a_v^(-1))^(-1)) <= A_Delta,       (CCC1)
Area_R([c_w,h_v]) <= A_0                                  (CCC2)
```

for every vertex `v` and every oriented edge `(v,w)`.  Then every
homomorphism from `Gamma` to a norm matrix corona kills `z`:

```text
z in Rad_MF(Gamma).                                        (CCC3)
```

If `z` normally generates `Gamma`, then `Rad_MF(Gamma)=Gamma`.

More quantitatively, let `N_d(delta)` be the least number of operator-norm
sets of diameter less than `delta` covering `U(d)`.  For a finite graph with

```text
chi(G)>N_d(delta),
```

every `d`-dimensional presentation tuple satisfies

```text
||z(U)-I||_op
 <= (A_Delta+A_0) Def_R(U)+2 delta.                        (CCC4)
```

One may use the explicit crude bound

```text
N_d(delta) <= (1+4 sqrt(d)/delta)^(2d^2).                 (CCC5)
```

The same proof works for approximation by arbitrary compact groups with
bi-invariant metrics whenever the commutator map is uniformly Lipschitz in
its first variable.

