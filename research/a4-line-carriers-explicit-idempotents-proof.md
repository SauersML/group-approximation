---
rg: 2
id: a4-line-carriers-explicit-idempotents-proof
kind: route
title: Character orthogonality identifies the spectral line carriers
target: a4-line-carriers-explicit-idempotents
requires:
  - a4-regular-line-sector-spectral-split
---

The abelianization of `A4` is cyclic of order three.  Hence every character
`chi` of `<a>` extends uniquely to a one-dimensional character `xi_chi` of
`A4`, and every element of the Klein four subgroup, in particular `b`, maps to
`1`.

For any finite group, the usual character idempotent

```text
E_chi=(1/12) sum_(g in A4) conjugate(xi_chi(g)) rho(g)
```

is central and acts as identity on the `xi_chi`-isotypic summand and as zero on
every inequivalent irreducible summand.  This follows directly from Schur
orthogonality: on an irreducible `pi`, the sum is an intertwiner, hence scalar,
and its trace is `1` for `pi=xi_chi` and `0` otherwise.

Now specialize to a regular multiple.  By
`a4-regular-line-sector-spectral-split`, inside the `P_chi` sector the operator
`P_chi Q_+ P_chi` has eigenvalue `1` precisely on the `xi_chi` summand and
eigenvalue `1/3` on the three-dimensional irreducible contribution.  Therefore
its spectral projection for `[2/3,1]` is exactly `E_chi`.

In one regular copy `xi_chi` occurs once, so `E_chi` has rank one out of twelve;
regular amplification preserves normalized trace `1/12`.

Finally every `g in A4` is one of finitely many fixed words in `a,b`.  If two
representations differ by at most `eps` on `a,b`, unitary telescoping bounds the
difference of each corresponding word by its fixed word length times `eps`.
Averaging the twelve bounds gives the asserted multiplicity-independent
`O(eps)` continuity of `E_chi`.