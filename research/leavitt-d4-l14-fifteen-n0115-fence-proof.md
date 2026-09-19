---
rg: 2
id: leavitt-d4-l14-fifteen-n0115-fence-proof
kind: route
title: Exhaust both normal fifteen-winner 0;115 boundary branches
target: leavitt-d4-l14-fifteen-n0115-is-fenced
requires:
  - leavitt-d4-l14-fifteen-n0115-carriers-are-explicit
  - maximal-noncrossing-forest-criterion
---

After the exact projection substitution, the middle five-syllable carrier has
the two exhaustive branches described in the carrier compiler.  The remaining
carrier identities and boundary have lengths

```text
branch I:  12, 12, 42;
branch II: 12, 12, 50.
```

For every carrier identity the artifact generates **all** noncrossing
partitions maximal under coarsening, using the recursive forest criterion.  It
retains every coordinate image during Tietze elimination.  This produces
`83` joint coordinate states in branch I and `33` in branch II.

For each state the boundary calculation takes every normalized cyclic cut,
appends a fresh coordinate `q^-1` in each of the four possible target copies,
and again generates all coarsening-maximal forests.  The final Q-first replay,
MSI job `16683062`, returned

```text
             branch I   branch II
augmented words   1848        1100
boundary states    197         101
q nonempty           27           9
q free                0           0
direct kills           8           3
power kills           19           6
unresolved             0           0
```

A direct kill means that the cyclically reduced `q` image is itself one of the
residual relators up to cyclic conjugacy and inversion.  A power kill means
that `q` is a pure power of one generator and the gcd of the pure-power
residual exponents divides its exponent.  Thus every nonempty apparent mark is
already trivial in its carrier quotient.  The earlier jobs `16681784` and
`16682011` used generic Tietze ordering; `16683062` is the canonical terminal
audit because it eliminates the once-occurring formal target first.
