---
rg: 2
id: weak-bass-fixed-two-generator-torsion-free-tester
kind: claim
title: One two-generator torsion-free group tests the integral weak Bass conjecture
distinct_from:
  two-generator-fp-torsion-free-master-tester: that packages Whitehead, assembly, Farrell--Jones, class, and Kaplansky group-ring tests but does not include the weak Bass trace identity.
  kaplansky-three-properties-fixed-fp-torsion-free-tester: that concerns elements and idempotents in group rings over fields; this concerns two traces on the projective class group of the integral group ring.
  full-farrell-jones-fixed-fp-torsion-free-tester: that tests a substantially stronger coefficient-rich assembly conjecture; this is an exact tester for the weak Bass consequence alone.
---

There exists one two-generator finitely presented torsion-free group `E`,
simultaneously nonsofic and non-MF, such that

```text
E satisfies the integral weak Bass conjecture
  <=>
every torsion-free group satisfies the integral weak Bass conjecture.
```

Explicitly, for a group `G`, let

```text
epsilon_G, kappa_G: K_0(Z[G]) -> Z
```

be respectively the augmentation trace and the Kaplansky trace, the latter
being the coefficient of the identity in the ordinary matrix trace of an
idempotent. The displayed equivalence says

```text
epsilon_E = kappa_E
  <=>
epsilon_G = kappa_G for every torsion-free group G.
```

This is an exact reduction, not a proof of the weak Bass conjecture. It does
not assert the classical Bass conjecture, whose individual nonidentity
conjugacy-class components require additional control.

**ESTABLISHED 2026-08-30** by
[[weak-bass-two-generator-tester-proof]].
