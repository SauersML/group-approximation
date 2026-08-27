---
rg: 2
id: balanced-word-haar-small-ball-proof
kind: route
title: Cancel central phases and apply Avni--Glazer--Larsen on SU(n)
target: balanced-word-haar-small-ball
requires: []
artifacts:
  - research/artifacts/random-relator-density-repair-2026-08-18.md
---

Avni--Glazer--Larsen (arXiv:2402.11108) prove that for each nontrivial word
`w` there are dimension-independent positive small-ball constants on every
`SU(n)`.  For the finite set `W`, take the minimum exponent/radius after
rescaling the Hilbert--Schmidt metric by `1/sqrt(n)`; the radius-to-diameter
condition is unchanged by this normalization.

The multiplication map

```text
U(1) x SU(n) -> U(n),   (z,V) |-> zV
```

is a continuous surjective homomorphism with finite kernel, so product Haar
pushes to Haar.  Thus each Haar `U_i` may be sampled as `z_i V_i` with the
`V_i` jointly Haar in `SU(n)`.  Since `w in [F_k,F_k]`, its exponent sum in
every generator is zero and

```text
w(z_1 V_1,...,z_k V_k)=w(V_1,...,V_k).
```

The AGL bound therefore transfers verbatim from `SU(n)^k` to `U(n)^k` for
balanced words.  Averaging over the finite distribution `mu` gives the
integral inequality by Fubini, and Markov's inequality gives the stated
high-return-locus bound.
