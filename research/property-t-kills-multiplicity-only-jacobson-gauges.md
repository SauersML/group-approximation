---
rg: 2
id: property-t-kills-multiplicity-only-jacobson-gauges
kind: claim
title: Property T kills multiplicity-only Jacobson gauge ramps
artifacts:
  - research/kazhdan-hellinger-block-balance-proof.md
distinct_from:
  jacobson-property-t-and-finite-k-do-not-exactify-the-head: that warns that property T does not apply to an arbitrary normalized-HS approximate representation; this applies it to the genuine permutation representation on exact block labels.
  bounded-block-jacobson-microstates-also-collapse: that controls direct sums with bounded irreducible dimensions by compactness; this controls unbounded exact blocks when the only freedom is their multiplicity along a finite quotient orbit.
  scalar-rephased-toeplitz-sections-still-collapse-head: that rules out scalar phases in one finite-section model; this rules out slowly varying nonscalar block multiplicities.
---

**ESTABLISHED ANSATZ NO-GO.** Put

```text
Q=EL_28(F_2[z,z^(-1)])
```

and fix a finite Kazhdan set `Sigma` with constant `kappa>0).
Let `Omega` be any finite `Q)-set and let `p` be a probability
on `Omega`. Define the unmatched mass of a generator by

```text
h_s(p)=(1/2) sum_(omega in Omega)
              |p(s^(-1)omega)-p(omega)|.
```

If

```text
max_(s in Sigma) h_s(p) <= eta,                          (KHB1)
```

then there is a `Q)-invariant probability `p_bar), constant on
each orbit, such that

```text
||p-p_bar||_1
 <= min(2,4 sqrt(2 eta)/kappa).                          (KHB2)
```

Consequently, for every `Q)-translate pair of bounded block
observables `f` and `f after q^(-1)`,

```text
|sum p(omega)f(omega)
 -sum p(omega)f(q^(-1)omega)|
 <= 8 ||f||_infinity sqrt(2 eta)/kappa.                  (KHB3)
```

This applies to a broad finite-window microstate ansatz. Suppose exact
kernel blocks are indexed by a finite `Q)-set, with normalized block
dimensions `p(omega)`, and each Laurent actor matches the prescribed
blocks except for a fraction `h_s(p)) of padding. If the padding is
`o(d)), then `eta=o(1)), so every two conjugate finitary-root
profiles have asymptotically equal trace and squared
Hilbert--Schmidt length.

In particular, a slowly varying multiplicity ramp cannot make the
Toeplitz closing defect negligible while retaining a conjugate
Jacobson head at positive density. Property T supplies a dimension-free
modulus **inside this exact-label ansatz**.

This does not prove head collapse for arbitrary microstates. A general
actor may coherently mix block labels rather than partially match them,
and then no genuine permutation representation of `Q` on
`Omega` has been extracted. That coherent mixing is the surviving
nonscalar escape.

DERIVATION
kazhdan-hellinger-block-balance-proof
