---
rg: 2
id: finite-packet-localized-return-centralizes-after-power
kind: claim
title: A localized return on a noncentral finite packet promotes to a central return after one fixed power
distinct_from:
  finite-normalizer-star-no-go: that retains a marked Plancherel countermodel for swap stars acted on by packet automorphisms; this starts from an asserted localized return and shows quantitatively that noncentrality of its finite packet gives no extra freedom.
  finite-support-central-corners-are-finite-normal-twisted-sectors: that classifies projections central in the whole ambient group algebra; the promoted projection here need only be central in the finite packet algebra and in the resulting local direct-product carrier.
  finite-graph-packet-compression-wandering-no-go: that uses Bass--Serre support orthogonality for a finite graph of finite groups; this applies to any ambient finitely presented group once the marked word normalizes one finite packet.
---

Let `Gamma=<S|R>` be finitely presented, let `K<=Gamma` be finite, let
`w in Gamma` normalize `K`, and suppose that `w` has infinite order.  Let

```text
0!=q=q*=q^2 in C[K].                                  (FPR1)
```

Put `r=ord(Ad(w)|K)`.  There is a nonzero projection

```text
p in Z(C[K])                                           (FPR2)
```

depending only on `(K,q)` such that the following quantitative implication
holds.  After exactifying the fixed `K` packet, if an approximate
representation satisfies

```text
||(W^2-I)Q||_2 <= epsilon                              (FPR3)
```

and has covariance error at most `gamma` on the finitely many equalities

```text
[w^(2r),k]=1,                 k in K,                  (FPR4)
```

then, for one constant `C_(K,q)<infinity`,

```text
||(W^(2r)-I)P||_2
 <= C_(K,q) (r epsilon+gamma).                         (FPR5)
```

In a fixed finite presentation `gamma=O(defect+exactification error)`, so a
matrix-only square return on an arbitrary noncentral finite packet always
promotes to an identity return for the infinite-order word `w^(2r)` on the
central packet `p`.

The local carrier contains no remaining twisted-Laurent obstruction.  Since
`w^(2r)` centralizes `K` and has infinite order,

```text
<K,w^(2r)> ~= K times Z.                               (FPR6)
```

Its quotients `K times Z/N` give exact canonical finite models, and for every
`N>1`, writing `g=w^(2r)`,

```text
||(lambda_N(g)-I)lambda_N(p)||_2^2=2 tau(p)>0.          (FPR7)
```

Consequently neither a noncentral finite-normal packet nor a projective
twisted-Laurent description can itself prove the localized return.  After
one fixed power and Reynolds averaging it has become a central packet in the
residually finite direct product `(FPR6)`.  Any successful use of such a
packet must obtain `(FPR3)` from ambient relations outside this local
finite-by-cyclic carrier; packet noncentrality, cyclic holonomy, and finite
projective phases do not supply the matrix-only step.

