---
rg: 2
id: classical-bass-fixed-two-generator-testers
kind: claim
title: One fixed two-generator group tests the classical Bass conjecture in each universal lane
distinct_from:
  weak-bass-fixed-two-generator-torsion-free-tester: that compares only the augmentation and identity-coefficient traces in the torsion-free lane; this controls every nonidentity conjugacy-class component and also gives an all-group tester.
  bost-fixed-two-generator-torsion-free-tester: that tests an analytic assembly conjecture with separable coefficients; this tests its integral Hattori--Stallings consequence directly.
  two-generator-fp-torsion-free-master-tester: that packages Whitehead, assembly, Farrell--Jones, class, and Kaplansky equivalences; its Bass consumer is supplied by the torsion-free half of this theorem.
---

For a group `G`, write

```text
HS_G:K_0(Z[G]) -> direct_sum_[g in Conj(G)] Z[g]
```

for the Hattori--Stallings trace. The integral classical Bass conjecture for
`G` says

```text
image(HS_G) is contained in Z[1].
```

There are fixed two-generator finitely presented groups `U` and `E`
such that

```text
U satisfies classical Bass
  <=>
every group satisfies classical Bass,
```

and

```text
E satisfies classical Bass
  <=>
every torsion-free group satisfies classical Bass.
```

Here `Tord(U)={2,3,4,...}`, while `E` is torsion-free. Both can be
chosen nonsofic and non-MF. They are the same hosts as in
[[two-generator-frattini-universal-containers]], not newly enlarged groups.

These are exact reductions, not proofs of the classical Bass conjecture in
either lane.

**ESTABLISHED 2026-08-31** by
[[classical-bass-fixed-testers-proof]].
