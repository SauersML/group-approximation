---
rg: 2
id: bs14-one-power-level-is-a-native-short-commutator
kind: claim
title: The dyadic one-power level is one native linear-length BS commutator row
distinct_from:
  regular-bs14-cores-admit-dyadic-one-power-shadows: that constructs a regular-branch exact core killed by the power 4^K-1; this shows that its level row has a presentation of length O(K) using the already exact BS dynamics.
  repeated-squaring-and-tau-do-not-supply-the-moving-basin: that refutes a generic auxiliary repeated-squaring compression as a source of a stability radius; this uses no auxiliary variables and records an exact identity internal to the BS core, while retaining the same basin warning.
  fixed-level-bs14-compatible-basin: that asks whether the preconditioned tuple lies in the finite quotient's repair neighborhood; shortening one exact row does not prove that comparison.
---

In every group, or for every exact unitary pair, satisfying

```text
r s r^(-1)=s^4,                                      (NSC1)
```

one has for every `K>=1`

```text
[r^K,s]=r^K s r^(-K)s^(-1)=s^(4^K-1).               (NSC2)
```

Consequently, over the exact `BS(1,4)` row, the two quotient rows

```text
s^(4^K-1)=1,
[r^K,s]=1                                             (NSC3)
```

are equivalent.  The latter has ordinary word length `2K+2`.  Thus the
finite Iwahori target selected by the dyadic regular-branch shadow has a
presentation whose new level constraint is one native linear-length word;
it needs neither the exponentially long written power nor auxiliary
repeated-squaring registers.

The cores in
`regular-bs14-cores-admit-dyadic-one-power-shadows` satisfy this commutator
row exactly.  This improves the syntax of the moving target but does not
produce its missing normalized-Hilbert--Schmidt stability basin.  In
particular a direct word comparison of two generator pairs loses `O(K)`,
and `(NSC2)` is an exact-core identity: propagating a defect through `K`
fourth-power conjugations in a raw approximate core can be still worse.
