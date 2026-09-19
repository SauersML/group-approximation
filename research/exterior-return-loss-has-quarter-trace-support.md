---
rg: 2
id: exterior-return-loss-has-quarter-trace-support
kind: claim
title: A vanished exterior return has off-edge support of physical trace at least one quarter
distinct_from:
  kt-return-expectation-pays-one-full-edge-principal-angle: That turns return-expectation loss into one unnormalized superoperator principal angle; this extracts a padding-stable normalized matrix vector and a positive physical support projection from the same return.
  kt-infinite-index-returns-force-divergent-edge-leakage: That sums arbitrarily many exterior returns to force an unbounded superoperator Hilbert--Schmidt norm; this needs only one return and obtains a fixed physical-trace support lower bound.
  vanishing-weight-block-carries-full-actor-edge-leakage: That puts divergent unnormalized leakage on a vanishing physical block while its return expectation tends to one; this proves that return expectation tending to zero rules out exactly that padding escape.
---

Use the notation of
`kt-return-expectation-pays-one-full-edge-principal-angle`.  Thus

```text
x=T^*phi(gamma)T,             P=E_B,
q=||E_B(phi(h))||_2,
eta=||phi(h)-x||_2,
y=(1-P)x.                                             (QTS1)
```

Let `p=supp(|y|)` be the right support projection of `y` in the physical
matrix algebra.  Then

```text
||y||_2^2 >=1-(q+eta)^2,
||y||_infinity<=2,
tr(p)>= [1-(q+eta)^2]/4.                              (QTS2)
```

In particular, if the exterior return expectation and fixed-word error
vanish, then

```text
||y||_2->1,                     liminf tr(p)>=1/4.     (QTS3)
```

This is invariant under arbitrary common padding: the normalized `L2` norm
and physical trace in `(QTS2)` are those of the complete matrix coordinate.
Therefore the divergent leakage required by the Kun--Thom relative model
cannot be exported entirely to a summand of vanishing physical trace once
even one fixed exterior-return expectation vanishes.

The conclusion is a carrier statement, not yet an actor contradiction.  The
projection `p` need not reduce `B`, be invariant under `Gamma`, or be
transported coherently by the other actor generators.  The remaining
Certificate C problem is to authenticate such a reducing/invariant carrier,
or to control the return vector by fixed presentation residuals without a
moving-radius loss.

DERIVATION
exterior-return-quarter-trace-proof
