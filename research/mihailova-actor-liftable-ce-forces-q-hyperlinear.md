---
rg: 2
id: mihailova-actor-liftable-ce-forces-q-hyperlinear
kind: claim
title: A projectively actor-liftable Connes embedding of the Mihailova Bernoulli product forces Q hyperlinear
distinct_from:
  mihailova-left-right-local-models-do-not-see-q: that proves arbitrary finite metric orbit patches exist universally; this identifies the additional matricial lift that promotes the lamp orbit to genuine finite-dimensional unitary coefficients.
  coordinate-action-not-sofic: that excludes Cartan permutation models for the Kun--Thom action; this is a representation-theoretic implication for the Mihailova left-right action and does not assume a diagonal Cartan.
---

Let `pi:F_m->Q`, put `G=F_m x F_m`, and let `G` act on `Q` by

```text
(u,v).q = pi(u) q pi(v)^(-1).
```

Write

```text
B = L^infinity({-1,1}^Q),       M = B rtimes G,
```

let `a_q in B` be the mean-zero Rademacher lamp at `q`, and let `w_g` be the
canonical actor unitaries.  Suppose that a Connes embedding

```text
Theta:M -> product_omega M_(d_n)
```

is **projectively actor-liftable**: there are maps
`V_n:G->U(d_n)` which are genuine projective representations (equivalently,
`Ad V_n:G->U(L^2(M_(d_n)))` is an exact representation) such that

```text
Theta(w_g) = [(V_n(g))_n]                           (AL1)
```

for every `g in G`.  Then the quasi-regular representation of `G` on
`ell^2(Q)` is weakly contained in finite-dimensional unitary
representations.  Consequently `Q` is hyperlinear.

No Cartan hypothesis and no removal of scalar cocycles is needed.  In
particular, the commonly proposed Cartan/normalizer condition is sufficient
at the following sharp threshold: if `Theta(B)` is diagonal and the
normalizers `Theta(w_g)` admit representatives whose conjugation actions, at
every matrix level, form an exact action of `G` (the monomial representatives
may multiply only projectively), then `(AL1)` holds and `Q` is hyperlinear.

Thus, **if** `Q` is separately known to be nonhyperlinear, every hypothetical
Connes embedding of `M` must be projectively actor-nonliftable.  The explicit
Mihailova input currently available is only known to be nonsofic, so the
conclusion `Q` hyperlinear is compatible with that candidate and does not
decide its crossed product.  Merely placing `B` in a diagonal ultraproduct
and representing its normalizers by permutations in the ultraproduct is not
enough: those representatives satisfy the `F_m x F_m` relations only modulo
normalized Hilbert--Schmidt/Hamming error.  Turning them into exact
levelwise projective representations is precisely the missing stability
step.

This separates the two questions sharply:

- ordinary Connes embeddability gives matrix microstates for `M` and hence
  only approximate actor representations;
- projectively actor-liftable Connes embeddability gives exact
  finite-dimensional conjugation representations carrying the canonical
  lamp coefficient, which already
  detects hyperlinearity of `Q`.
