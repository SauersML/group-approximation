---
rg: 2
id: homogeneous-quotient-ce-forces-sl3-outlier-at-large-primes
kind: claim
title: At p at least 11 the only obstruction to the collapse is an SL3(Z) outlier -- deep towers are ruled out unconditionally
distinct_from:
  sl3-homogeneous-quotient-crossed-product-is-connes-embeddable: that is the open two-sided embeddability question; this is an UNCONDITIONAL structural theorem about what any embedding would have to look like on the lattice, with no stability hypothesis.
  sl3-large-prime-pair-relative-commutant-collapse: that is the collapse claim, whose truth needs the outlier sector removed; this is the unconditional half -- the near-genuine sector is already empty at p >= 11 -- isolating exactly the outlier obstruction.
  p-divisible-lambda-exact-mass-vanishes-at-large-primes: that bounds the p-divisible weight of a near-genuine microstate; this combines it with the deep-tower upper bound to eliminate the entire near-genuine sector of the crossed product, leaving only outliers.
---

**THEOREM (established here; proof in
`homogeneous-quotient-ce-outlier-proof`).**  Fix a prime `p >= 11` and a
torsion-free cocompact lattice `Lambda' < SL_3(Q_p)` with at least two
`SL_3(Z_p)`-orbits on `X = SL_3(Q_p)/Lambda'`, and let

```text
M_p = L^infinity(X) rtimes SL_3(Z[1/p]).
```

If `M_p` is Connes embeddable, then every matrix realization of a
trace-preserving embedding restricts on `SL_3(Z)` to a regular-type
hyperlinear approximation `(rho_n)` that is, along the ultrafilter,
uniformly bounded away in the **flexible** sense from genuine
finite-dimensional unitary representations: even after enlarging the
coordinate space from dimension `d_n` to `d_n+o(d_n)`, no compression of a
genuine representation is `o(1)`-close on lattice generators.  Such a
sequence is an **outlier**.  Equivalently,

```text
M_p Connes embeddable  =>  SL_3(Z) is not weakly ucp-stable
                            on regular-type hyperlinear approximations.
```

Contrapositively, `sl3-z-weakly-ucp-stable` implies `M_p` is not Connes
embeddable, hence (by
`homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse` read in the
established direction, and the HNN reduction) that
`G_p = <SL_3(Z[1/p]), t | [t, SL_3(Z)] = 1>` is non-hyperlinear.

**What is unconditional here.**  The elimination of the near-genuine sector
uses no stability hypothesis.  It is the conjunction of two established
theorems:

- `homogeneous-quotient-near-genuine-microstates-are-deep` `(DT2)` at level
  `j = 0`: a near-genuine microstate of `M_p` has coprime-level weight
  `nu_0 <= 1 - 1/(8 r) + O(epsilon)`, where `r >= 2` is the number of
  `SL_3(Z_p)`-orbits (the `K`-orbit cell family forces positive `p`-adic
  content, because the lamp `U` is `SL_3(Z)`-central but not
  `SL_3(Z[1/p])`-central and its cell structure lives at every congruence
  level);
- `p-divisible-lambda-exact-mass-vanishes-at-large-primes`: a near-genuine
  microstate has `p`-divisible weight `1 - nu_0 <= C epsilon^2/kappa_0^2`,
  so `nu_0 -> 1`.

The two are incompatible in the limit, so `M_p` has no near-genuine
microstate sequence at all: every embedding is carried by outliers.  This is
the sharpest unconditional statement the depth-free machinery yields, and it
identifies the outlier sector -- not deep towers, not the p-divisible sector
-- as the sole remaining obstruction at every large prime.

## Attempts

- **Can the outlier sector be removed unconditionally?**  No tool in the
  graph does this.  An outlier is an approximate representation of `SL_3(Z)`
  with no congruence-level structure, so neither the type decomposition of
  the depth-free argument nor the cell structure of the deep-tower argument
  applies to it.  Removing it is exactly `sl3-z-weakly-ucp-stable`, an open
  Positivstellensatz-type stability question; strong property (T)
  (Lafforgue) controls uniformly bounded approximate representations near the
  trivial representation, not regular-type HS approximations, so it does not
  close the sector.
- **Does non-embeddability of `M_p` give a non-hyperlinear group directly?**
  No.  `M_p` is a crossed product, not a group von Neumann algebra, so its
  non-embeddability is a non-hyperlinear *tracial algebra*, not a group; the
  group `G_p` is produced only through the collapse and the HNN reduction,
  which need the outlier sector handled.
