---
rg: 2
id: even-partial-swap-star-has-canonical-trace-floor
kind: claim
title: An even star of orthogonal partial-isometry swaps has a canonical trace floor
distinct_from:
  partial-isometry-swap-wordizes-one-bcs-gram-row: that compares a swap commutator with one BCS Gram row; this multiplies swaps sharing one source and obtains a dimension-free trace obstruction without a game.
  closed-multiplicity-cycle-kills-carrier-trace: that assumes decoded source and target projections already close around a multiplicity cycle; this gives an explicit one-word Hilbert-hotel checksum for an orthogonal star in a two-copy matrix chart.
  approximate-relative-leavitt-cell-kills-active-trace: that subtracts the traces of decoded additive Leavitt equations; this reads the contradiction from the trace of one product of involutive swaps.
---

Let `(M,tau)` be a finite tracial matrix algebra.  Fix an even integer
`k>=2`.  Let `Q` be a projection and let `S_1,...,S_k` be partial
isometries with one common initial projection and pairwise orthogonal range
projections:

```text
S_i^*S_i=Q,
P_i=S_iS_i^*,
P_iP_j=0                 (i!=j).                       (ESS1)
```

In `M_2(M)` form the partial-isometry swaps

```text
J_i=[[I-P_i, S_i],
     [S_i^*, -(I-Q)]].                                (ESS2)
```

Each `J_i` is a self-adjoint involution.  Put

```text
h_k=J_1J_2...J_k.                                     (ESS3)
```

### Theorem

Exactly,

```text
tau_2(h_k)=1-((k+1)/2)tau(Q),                         (ESS4)
```

and consequently

```text
tau_2(h_k)>=(k-1)/(2k).                               (ESS5)
```

The bound is independent of the matrix dimension and tends to `1/2` as
more orthogonal children are added.  For the binary cell,

```text
tau_2(J_1J_2)>=1/4.                                   (ESS6)
```

This is an explicit error-spreading checksum: copying one finite source
into more mutually incompatible regions makes the canonical-trace mismatch
larger, rather than easier to dilute.

## Proof

Decompose the top copy of the two-copy Hilbert space as

```text
(directSum_i P_i H) directSum (I-sum_i P_i)H          (ESS7)
```

and the bottom copy as `QH directSum (I-Q)H`.  Identify every `P_iH`
with `QH` by `S_i`.  On

```text
QH_bottom directSum P_1H_top directSum ... directSum P_kH_top,
                                                                    (ESS8)
```

the involution `J_i` is the star transposition exchanging the source copy
with the `i`-th range copy and fixing the other range copies.  Their product
is a `(k+1)`-cycle, so its operator trace on `(ESS8)` is zero.

Every `J_i` is the identity on the top complement in `(ESS7)`.  It is
`-I` on `(I-Q)H` in the bottom copy, and the product is the identity there
because `k` is even.  Therefore the only trace comes from those two fixed
complements, giving

```text
tau_2(h_k)
 =1/2[(1-k tau(Q))+(1-tau(Q))]
 =1-((k+1)/2)tau(Q).                                  (ESS9)
```

Orthogonality of the ranges gives

```text
k tau(Q)=sum_i tau(P_i)=tau(sum_i P_i)<=1.            (ESS10)
```

Substituting `(ESS10)` into `(ESS4)` proves `(ESS5)`.  ∎

## Robust use

Suppose a fixed packet exactification replaces decoded matrices by data
satisfying `(ESS1)--(ESS2)` while moving each named swap by at most
`epsilon` in normalized `2`-norm.  Word telescoping moves `h_k` by at most
`k epsilon`, hence

```text
Re tau_2(h_k(U)) >= (k-1)/(2k)-k epsilon.             (ESS11)
```

If the abstract word `h_k` is nonidentity, canonical-trace microstates
instead require `tau_2(h_k(U))->0`.  Therefore a finite ordinary-word
compiler for this one common-source orthogonal swap star would already
produce a non-hyperlinear group.  The remaining issue is not the trace
ledger: it is authenticating the common source and orthogonal range chart
from ordinary group relators without admitting an unrelated finite
`S_(k+1)` representation.

Exact infinite completeness is compatible with the geometry.  On a
separable infinite-dimensional Hilbert space, one source is isomorphic to
`k` pairwise orthogonal infinite ranges, and `(ESS2)` gives exact swaps with
`h_k` nonidentity.  The obstruction in `(ESS5)` is specifically finite
tracial rank.

## Attempts

- **Use only the Coxeter relations of the swaps.**  This retains a finite
  symmetric-group model; the two-copy common-source chart is not encoded.
- **Transport separate sources around a cycle.**  The stationary coordinate
  model in `cyclic-conjugacy-does-not-synchronize-swap-sources` is exact.
- **Decode the common-source orthogonal chart first.**  This succeeds
  analytically: `(ESS4)--(ESS5)` are the complete trace endpoint.  The open
  work has been separated into
  `common-source-orthogonal-partial-swap-star-compiler`.
