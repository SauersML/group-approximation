---
rg: 2
id: master-host-satisfies-algebraic-strong-atiyah
kind: claim
title: The two-generator torsion-free master tester satisfies Strong Atiyah over the algebraic numbers
distinct_from:
  strong-atiyah-torsion-free: that is the conjecture for every torsion-free group over the complex numbers; this is one group over the algebraic numbers, equivalent by subgroup permanence to the recursively presented torsion-free case.
  algebraic-strong-atiyah-for-all-torsion-free-groups: that quantifies over all torsion-free groups; this is the single host, which reaches all of them only together with the determinant conjecture.
---

**OPEN.**  `E` is the witness of `two-generator-fp-torsion-free-master-tester`.
Every countably generated recursively presented torsion-free group embeds in
`E`, and Strong Atiyah passes to subgroups (Step 1 of
`algebraic-atiyah-determinant-colimit-proof`).  So this claim is equivalent to
Strong Atiyah over `Qbar` for all countably generated recursively presented
torsion-free groups.  Together with
`master-host-satisfies-determinant-conjecture` it gives Strong Atiyah over
`Qbar` for every torsion-free group
(`algebraic-atiyah-and-determinant-one-group-tester`).

A counterexample may be sought over any torsion-free group: if `Det(E)`
holds, a non-integral kernel dimension over any torsion-free `H` forces one
over `E` by the same tester.

Without any determinant hypothesis this claim already has an algebraic payoff:
it makes `Qbar[G]` embed in a division ring for every torsion-free group `G`
(corollary in `division-ring-embedding-torsion-free-one-group-tester`).  So a
torsion-free group algebra over `Qbar` with no division-ring embedding, for
instance one with a zero divisor, refutes this claim.

## Attempts

* **Sofic Lueck approximation.**  Dead:
  `master-host-atiyah-via-sofic-luck-approximation`.
* **Hughes-free division rings of locally indicable groups.**  Dead:
  `master-host-atiyah-via-locally-indicable-hughes-free`.
* **Linnell's class `C`.**  Dead: `master-host-atiyah-via-linnell-class-c`.

All three die at `universal-torsion-free-hosts-not-sofic-or-locally-indicable`.
Any proof must work for a nonsofic group containing infinite finitely
presented torsion-free Kazhdan subgroups, including the Fournier--Facio group,
where no finite approximation is available and no epimorphism onto `Z` exists.
