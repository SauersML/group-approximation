---
rg: 2
id: multiplicity-pi-turing-tape
kind: claim
title: A finite-group isotypic multiplicity block is a matrix tape detected by Amitsur--Levitzki
artifacts:
  - research/artifacts/kleene-self-destroying-hs-pcp-boone-2026-08-20.md
distinct_from:
  multiplicity-return-transducer: that asks a finite network to return a fixed-size Schur--Clifford packet with an extensive multiplicity surplus; this identifies the raw multiplicity algebra itself as a dimension-sensitive computation tape.
  pure-finite-group-operator-scaling-collapses-to-multiplicity: that records that a finite-group label factor leaves arbitrary multiplicity; this turns that surviving multiplicity into the input of a polynomial-identity detector.
---

Let `H` be a finite group, let `pi` be an irreducible complex representation
of dimension `r`, and let `Q` be the `pi`-isotypic projection in an exact
finite-dimensional unitary representation.  For some multiplicity `k`,

```text
Q C^d = C^r tensor C^k,
rho(H)|_Q = pi(H) tensor I_k,
Comm(rho(H))|_Q = I_r tensor M_k(C).                               (MPT1)
```

If two tape elements `x,y` centralize `H`, their restrictions to this block
have the form `I_r tensor X` and `I_r tensor Y`.  The polynomials of
`two-generator-amitsur-levitzki-dimension-oracle` therefore satisfy

```text
p_k(x,y)|_Q = I_r tensor p_k(X,Y) = 0.                             (MPT2)
```

Thus the rectangular escape `fixed label factor tensor arbitrarily large
multiplicity` is exactly an `M_k(C)` tape, and increasing multiplicity only
moves the zero trigger to a later instruction.

This is an exact representation-theoretic statement.  In an approximate
microstate one still needs simultaneous exactification of `H`, a
positive-density `pi` carrier, finite compilation of the unbounded instruction
sequence, and a dimension-independent way to propagate `(MPT2)` to a fixed
marked-word defect.  In particular the degree growth of `p_k` prevents using
naive word telescoping as the quantitative propagation step.

