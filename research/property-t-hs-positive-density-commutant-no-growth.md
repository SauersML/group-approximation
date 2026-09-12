---
rg: 2
id: property-t-hs-positive-density-commutant-no-growth
kind: claim
title: Property (T) forbids positive-density adjoint commutant growth in normalized-HS microstates
distinct_from:
  commutant-no-growth: that gives exact equality of commutants in genuine finite-dimensional representations by integer dimension; this gives an O(delta) density estimate for approximate representations.
  commutant-density-trace-blind: that shows the absolute normalized commutant density vanishes on regular-character limits; this controls the relative mass of new low-energy directions and remains informative when a packet supplies positive density.
  corona-commutant-growth-witness: that exhibits zero-density slow walls in an operator-norm corona; this excludes only positive normalized adjoint density and is compatible with such slow walls.
---

Let `Gamma=<S>` have property `(T)`, with `S` finite and inverse closed, and
let `alpha:Gamma->Gamma` be an injective endomorphism. Write every
`alpha(s)` as one fixed word `w_s` over `S`, and form the ascending-HNN
relations

```text
t s t^(-1)=w_s,                 s in S.                          (PCG1)
```

There are fixed cutoffs `0<a<b<c<kappa/2` and a constant `C` such that every
inverse-normalized normalized-HS `delta`-microstate on a sufficiently large
finite window has the following property. On the normalized adjoint Hilbert
space `L^2(M_d)`, put

```text
A=I-(1/|S|)sum_(s in S) Ad(phi(s)),
C_alpha=I-(1/|S|)sum_(s in S) Ad(phi(w_s)),
P=1_[0,a](A),                  Q=1_[0,b](C_alpha).
```

Then

```text
tr_ad(Q(I-P)) <= C delta.                                      (PCG2)
```

Here `tr_ad` is normalized by `d^2`. Thus the compressed copy can create at
most `O(delta)` new low-adjoint-energy directions outside the original
low-energy space. In particular, any local packet construction producing a
subspace `W` with

```text
W<=Q,        W perpendicular P,        tr_ad(W)>=eta
```

forces `delta>=eta/C`.

The conclusion is intentionally a **positive-density** theorem. It neither
constructs exact commutants nor excludes walls whose adjoint rank is `o(d^2)`.

