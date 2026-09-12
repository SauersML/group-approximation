---
rg: 2
id: orthogonal-compressed-word-branches-have-cuntz-rank-floor
kind: claim
title: Orthogonal compressed unitary branches have the exact finite Cuntz rank floor
distinct_from:
  approximate-relative-leavitt-cell-kills-active-trace: that compares two inverse products with one additive range relation and obtains a linear trace bound; this uses only ambient unitary compressions and obtains a squared-HS rank floor without inverse or range-sum equations.
  fanizza-compressed-unitary-has-guarded-rank-floor: that treats one compression into a target missing a guarded subprojection; this treats an arbitrary orthogonal Cuntz family and sums the full child-capacity deficit.
  even-partial-swap-star-has-canonical-trace-floor: that assumes exact common-source partial isometries and reads a product-word trace; this permits arbitrary compressed unitary words and charges failure of their source Grams directly.
  universal-block-return-violates-the-regular-firewall: that rules out a fixed two-product proper-corner identity by trace cyclicity; this gives the sharp k-branch finite rank inequality and its exact stabilized infinite realization.
---

Let `(M_d(C),tr_d)` have normalized trace.  Let `E` be a projection, let
`Q_1,...,Q_k<=E` be pairwise orthogonal projections, and let `U_1,...,U_k`
be arbitrary unitaries.  Put

```text
X_i=Q_i U_i E.                                         (OCB1)
```

Then the exact finite-dimensional inequality is

```text
sum_i ||X_i^*X_i-E||_2^2
 >= k tr_d(E)-sum_i tr_d(Q_i)
 = (k-1)tr_d(E)+tr_d(E-sum_i Q_i).                    (OCB2)
```

In particular, for a binary proper-corner packet,

```text
||X_1^*X_1-E||_2^2+||X_2^*X_2-E||_2^2>=tr_d(E).      (OCB3)
```

The constant is independent of dimension, packet multiplicity, and the
ranks of the child cuts.  No inverse branches, off-diagonal Cuntz equations,
or assumption that the child ranges exhaust `E` is needed.

The sign is exactly the desired Hilbert-hotel sign.  On a separable
infinite-dimensional Hilbert space choose `E`, all `Q_i`, and all their
orthogonal complements infinite dimensional, with the `Q_i` orthogonal
below `E`.  There are ambient unitaries `U_i` carrying `EH` onto `Q_iH`, so

```text
X_i^*X_i=E                         for every i,         (OCB4)
```

while `E!=0`.  Thus the exact infinite marked model survives after harmless
infinite stabilization, whereas every finite normalized trace pays `(OCB2)`.

There is also a sharp word-realization firewall.  Let `K<=Gamma` be a finite
marked packet, let `0!=E in M_n(C[K])` be its marked source projection, let
the `Q_i` be fixed orthogonal packet projections below `E`, and let the
`U_i` be fixed unitary word matrices over `C[Gamma]`.  If the group relators
imply
`(OCB4)` in every unitary representation, then applying `(OCB2)` in
`M_n(L(Gamma))` gives

```text
(k-1)tau_n(E)=0.                                      (OCB5)
```

Faithfulness of the regular trace forces `E=0`, contradicting packet
embedding.  Hence the compressed source-fullness equations cannot be
universal group-algebra identities.  A viable ordinary-word compiler may
use `(OCB2)` as its terminal finite-HS inequality, but the inference making
the source Grams small must be genuinely finite-matrix-only.

For `(CPS12)`, take `E` to be the common marked Gram source and the `Q_i` to
be orthogonal asynchronous child cuts.  Equation `(OCB2)` completely solves
the unequal-index rank ledger.  The only remaining datum is a packet decoder
which authenticates the compressed source Grams from group-word defects in
finite matrices without asserting `(OCB4)` in the regular representation.
