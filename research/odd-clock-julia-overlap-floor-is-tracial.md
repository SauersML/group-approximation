---
rg: 2
id: odd-clock-julia-overlap-floor-is-tracial
kind: claim
title: An odd cyclic clock gives a universal overlap floor, not a matrix-only Julia authenticator
distinct_from:
  periodic-bs-clock-defeats-spectral-first-hit-checksum: that gives large periodic clocks whose marginal first-hit atoms dilute; this computes the exact obstruction when a finite odd clock tries to rotate one half-rank projection toward its complement.
  julia-dilation-packages-heat-as-one-cross-gram-moment: that packages the small heat amplitude as an overlap; this shows why literal odd-period authentication of that overlap cannot be the finite-coordinate return.
  universal-block-return-violates-the-regular-firewall: that uses trace cyclicity for two returned products; this derives a separate quantitative floor from odd periodicity and projection geometry.
---

Let `(M,tau)` be a finite tracial von Neumann algebra, let `E in M` be a
projection with `tau(E)=1/2`, and let `C in U(M)` satisfy `C^n=1` for an odd
integer `n`.  Put

```text
Q=C^* E C,
a=tau(EQ).
```

Then

```text
a >= 1/(2n^2).                                       (OCJ1)
```

More generally, if `eta=||C^n-1||_2<1`, then

```text
a >= (1-eta)^2/(2n^2).                               (OCJ2)
```

Indeed set `S=2E-1` and `S_j=C^(-j)SC^j`.  Every adjacent antiphase defect
has the same norm

```text
delta=||S_1+S_0||_2.
```

Telescoping with alternating signs gives

```text
||S_n-(-1)^n S_0||_2 <= n delta.                     (OCJ3)
```

Since `n` is odd and approximate periodicity gives
`||S_n-S_0||_2<=2eta`, the left side needed to change `S_0` into `-S_0`
is at least `2-2eta`.  Thus `delta>=(2-2eta)/n`.  On the other hand

```text
delta^2
 =4||Q-(1-E)||_2^2
 =8 tau(EQ),                                         (OCJ4)
```

where the last equality uses `tau(E)=tau(Q)=1/2`.  This proves `(OCJ2)`.

Applied to the Julia projection `Q_(B_t)`, `(OCJ1)` says that a literal
odd-order group word rotating `E` to `Q_(B_t)` would lower-bound the heat
amplitude.  This does not authenticate a finite matrix coordinate.  The
proof above uses only the finite trace, so it runs unchanged in the regular
finite von Neumann algebra.  Adding such a clock as exact group relations
would either destroy the nonzero regular carrier or prevent the required
relations from holding; it cannot preserve the reverse-Kleene mark while
killing only finite-matrix realizations.

The same warning applies to commuting first-hit bands cut from this finite
orbit.  Their orthogonality and trace budget are tracial identities.  A
clock becomes relevant only after a separate matrix-coordinate decoder has
identified its half-rank carrier with the marked multiplicity reservoir.
