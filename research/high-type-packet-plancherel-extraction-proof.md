---
rg: 2
id: high-type-packet-plancherel-extraction-proof
kind: route
title: Remove bounded Kazhdan types from the finite-quotient Plancherel average
target: high-type-irreducibles-retain-finite-packet-mass
requires:
  - kazhdan-bounded-unitary-types-are-finite
---

For a quotient `q_n:Lambda->Q_n`, decompose the left regular representation
of `Q_n`.  If `sigma in Irr(Q_n)`, set

```text
a_sigma=dim(sigma)^2/|Q_n|,
r_sigma=tr_(dim sigma)(sigma(z)).
```

Injectivity on `B` identifies the regular trace of `z` in `Q_n` with its
regular trace `q` in `B`.  Since `z` is a projection,

```text
0<=r_sigma<=1,
sum_sigma a_sigma r_sigma=q.                           (1)
```

Fix `K`.  The pulled-back quotient irreducibles of degree at most `K` lie in
the finite set `Irr_<=K(Lambda)`.  If

```text
C_K=sum_(rho in Irr_<=K(Lambda)) dim(rho)^2,
```

their total Plancherel weight is at most `C_K/|Q_n|`, which tends to zero.
For large `n` it is less than `q/2`.  If every remaining irreducible had
`r_sigma<q/2`, the low-degree part of `(1)` would be less than `q/2` and the
high-degree part would also be less than `q/2`, contradicting `(1)`.  Hence
some `sigma` has degree greater than `K` and `r_sigma>=q/2`.  Letting `K`
tend to infinity gives the required sequence.  Schur's lemma gives its
normalized commutant density `1/dim(sigma)^2`.

If `q_n o alpha=q_n`, then `sigma q_n alpha=sigma q_n`; setting the HNN
stable letter to the identity extends the representation.  If instead the
two quotient maps differ by an automorphism implemented in `sigma`, use its
implementing unitary for the stable letter.  This proves the stationary-HNN
clause and the stated three-way fence.

