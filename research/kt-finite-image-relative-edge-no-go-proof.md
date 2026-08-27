---
rg: 2
id: kt-finite-image-relative-edge-no-go-proof
kind: route
title: Convert expectation accuracy into profinite separation of the edge
target: kt-finite-image-relative-edge-models-are-impossible
requires:
  - coordinate-action-not-sofic
---

For a fixed `g notin Gamma`, let

```text
Bad_n(g)={r:q_(n,r)(g) in q_(n,r)(Gamma)}.
```

On a block indexed by `r in Bad_n(g)`, the unitary
`pi_(n,r)(q_(n,r)(g))` lies in the corresponding summand of `B_n`, so the
trace-preserving expectation fixes it.  Orthogonality of the direct-sum
blocks gives

```text
||E_(B_n)(rho_n(g))||_2^2
  >= sum_(r in Bad_n(g)) mu_(n,r).                     (KFE4)
```

Thus `(KFE3)` makes the right side tend to zero for each fixed exterior
element.

Enumerate `G\Gamma={g_1,g_2,...}`.  For fixed `m`, the union bound gives

```text
sum_r mu_(n,r) 1_[some i<=m has r in Bad_n(g_i)]
 <=sum_(i<=m) sum_(r in Bad_n(g_i)) mu_(n,r) ->0.       (KFE5)
```

For large `n` there is therefore an index `r` of positive weight for which
none of `g_1,...,g_m` maps into the image of `Gamma`.  Choose that quotient
and, successively, take products of the chosen quotients.  The resulting
cofinal family satisfies

```text
intersection_m Gamma ker(q_m)=Gamma.                   (KFE6)
```

The finite coset actions on
`G/(Gamma ker(q_m))` then reproduce every prescribed finite piece of the
Schreier action on `G/Gamma`; in particular they are sofic approximations of
that action.  This contradicts `coordinate-action-not-sofic`.

