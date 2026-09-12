---
rg: 2
id: universal-torsion-free-hosts-not-sofic-or-locally-indicable
kind: claim
title: A group containing every finitely presented torsion-free group is neither sofic nor locally indicable
invalidates: [master-host-atiyah-via-sofic-luck-approximation, master-host-atiyah-via-locally-indicable-hughes-free, master-host-atiyah-via-linnell-class-c, master-host-determinant-via-elek-szabo, galois-invariance-via-sofic-luck-approximation]
distinct_from:
  fournier-facio-group-is-nonsofic: that is nonsoficity of one explicit group; this transfers it, together with the failure of local indicability and of membership in Linnell's class, to every universal torsion-free host.
---

Let `Omega` be a group containing an isomorphic copy of every finitely
presented torsion-free group.  Then

1. `Omega` is not sofic;
2. `Omega` is not locally indicable;
3. `Omega` is not in Linnell's class `C`, the smallest class containing the
   free groups and closed under directed unions and under extensions with
   elementary amenable quotient.

In particular the two-generator torsion-free master tester `E` of
`two-generator-fp-torsion-free-master-tester` has none of the three
properties, since every countably generated recursively presented torsion-free
group embeds in it.

## What it rules out

The universal case of Strong Atiyah is out of reach of each of these
techniques:

* the sofic Lueck approximation theorem and the base change from `Qbar` to
  `C` (Jaikin-Zapirain, GAFA 29 (2019), Theorems 1.3 and 1.1, cited as such in
  arXiv:2201.03268, Theorem 2.1 and Remark 3.8) need a sofic group;
* the theorem of Jaikin-Zapirain--Lopez-Alvarez covers locally indicable
  groups (Fisher--Ng, arXiv:2606.19606, Section 1.1; Lueck,
  arXiv:2102.04549v2, Theorem 3.3);
* Linnell's theorem covers class `C` (Lueck, same Theorem 3.3);
* the determinant conjecture is known for sofic groups (Lueck, same survey,
  Remark 3.11).

The four corresponding routes to `master-host-satisfies-algebraic-strong-atiyah`
and `master-host-satisfies-determinant-conjecture` are recorded dead.  So
Strong Atiyah and the determinant conjecture for all finitely presented
torsion-free groups are questions about a nonsofic group containing Kazhdan
subgroups, and approximation-based tools cannot decide them at the host.

**ESTABLISHED 2026-09-11** by [[universal-torsion-free-host-obstruction-proof]].
