---
rg: 2
id: adaptive-rectangular-kernel-column-extraction
kind: claim
title: Positive rectangular excess survives unbounded amplification by one-column extraction
distinct_from:
  fixed-rectangular-kernel-return-factorization-is-impossible: that forbids a fixed group-algebra factorization by evaluating it in the regular factor; this is a purely finite-matrix extraction theorem and permits the pencil size and coefficients to depend arbitrarily on the matrix model.
  unnamed-positive-density-fixed-space-is-terminal: that turns a contraction already living in the original matrix model into a canonical-character contradiction; this shows that a returned projection in an arbitrarily large rectangular amplification supplies exactly such a contraction.
  dimension-expander-sampler-is-not-a-fixed-proper-return: that fences a fixed square finite packet; this identifies the sharp density condition for genuinely rectangular, dimension-activated families.
---

Let `V in U(d)`, let `p>q`, and let `P` be an orthogonal projection on
`C^p tensor C^d`.  Normalize traces and Hilbert--Schmidt norms on every
matrix algebra.  Suppose

```text
tr_(pd)(P)>=alpha,
||(I_p tensor (V-1))P||_(2,pd)<=epsilon                 (ARK1)
```

for some `alpha>0`.  Then there is a contraction `X in M_d(C)` such that

```text
||X||_(2,d)^2>=alpha/2,
||(V-1)X||_(2,d)<=sqrt(2/alpha) epsilon.               (ARK2)
```

The constants do not depend on `p`, `q`, or `d`.  In particular, if
`P=1_(ker A)` for an arbitrary model-dependent map

```text
A:(C^d)^p -> (C^d)^q,
```

then rank--nullity supplies `(ARK1)` with
`alpha=(p-q)/p`.  Thus an unbounded, dimension-activated family of returned
rectangular kernels closes the unnamed-carrier endpoint whenever

```text
liminf (p-q)/p>0.                                      (ARK3)
```

## Proof

Write `P=(P_ij)_(1<=i,j<=p)` in `d`-dimensional blocks and put `D=V-1`.
For each column index set

```text
m_i=tr_d(P_ii),             e_i=tr_d(D P_ii D^*).
```

Since `P=P^2`, cyclicity gives

```text
(1/p) sum_i m_i = tr_(pd)(P)>=alpha,
(1/p) sum_i e_i = ||(I_p tensor D)P||_(2,pd)^2
                  <=epsilon^2.                        (ARK4)
```

Let `G={i:e_i<=2epsilon^2/alpha}`.  Markov's inequality gives
`|G^c|/p<=alpha/2`.  Since every `0<=P_ii<=1`,

```text
(1/p) sum_(i in G) m_i
 >= alpha-|G^c|/p
 >= alpha/2.                                           (ARK5)
```

Hence some `i in G` has `m_i>=alpha/2`.  Take
`X=P_ii^(1/2)`.  It is a contraction and

```text
||X||_2^2=m_i,
||(V-1)X||_2^2=tr_d(D P_ii D^*)=e_i,
```

which proves `(ARK2)`.

## Sharp dilution calibration

The fixed positive lower bound in `(ARK3)` is essential.  Let `V_d` be the
cyclic shift on `C^d` and let `Q_d` project onto its one-dimensional fixed
space.  Put

```text
p_d=d,             q_d=d-1,
P_d=I_(p_d) tensor Q_d.
```

Then `P_d` has exactly the rank forced by a `q_d`-by-`p_d` rectangular map:

```text
rank(P_d)=d=(p_d-q_d)d,
tr_(p_d d)(P_d)=1/d,
(I_(p_d) tensor (V_d-1))P_d=0.                        (ARK6)
```

There is a linear map
`A_d:(C^d)^(p_d)->(C^d)^(q_d)` with kernel `P_d`, because the orthogonal
complement of its range has dimension
`p_d(d-1)=q_d d`.  Meanwhile

```text
tr_d(V_d^k)=0                    (0<|k|<d).             (ARK7)
```

Thus these returned kernels coexist perfectly with every fixed finite
window of the canonical moments of an infinite-order word, while their
density tends to zero.  Mere strict inequality `p(d)>q(d)` is therefore not
a dimension-overflow obstruction.  A surviving adaptive pencil must either
have extensive excess `(ARK3)` or independently amplify its vanishing
kernel density.  Increasing the menu size alone does neither.

This theorem removes one possible ambiguity from the adaptive Hilbert-hotel
route.  Unbounded pencil size creates no analytic loss after a positive
relative deficiency has been obtained: one diagonal block returns the
carrier to the original `d`-dimensional microstate with uniform constants.
The only remaining hard step is the genuinely matrix-only semantic return
in `(ARK1)`; it cannot be a fixed or bounded-menu group-algebra
factorization by
`fixed-rectangular-kernel-return-factorization-is-impossible`.
