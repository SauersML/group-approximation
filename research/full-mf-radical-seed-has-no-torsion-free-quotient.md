---
rg: 2
id: full-mf-radical-seed-has-no-torsion-free-quotient
kind: claim
title: Some finitely presented full-MF-radical group has trivial universal torsion-free quotient, so no homomorphic-image transfer works on every input
distinct_from:
  torsion-generated-mf-absorbers-die-in-torsion-free-targets: that proves the binary-Leavitt absorbers in current use are torsion-generated and therefore die in every torsion-free quotient, which a better witness could in principle repair; this builds such an object out of an ARBITRARY full-MF-radical input, so the defect is a property of the input class and not of the witness in hand.
  torsion-free-central-cover-forces-abelian-finite-subgroups: that kills the class of procedures passing to a torsion-free CENTRAL cover above the input; this kills the class of procedures passing to a torsion-free QUOTIENT below it, and the two go in opposite directions.
  full-mf-radical-groups-form-an-extension-colimit-class: that lists the closure properties of the full-MF-radical class, including under amalgams over arbitrary vertex groups; this uses one specific amalgam whose vertex groups are NOT in that class -- each maps onto a finite cyclic group -- and whose amalgamating relation is what makes the total group full.
artifacts:
  - research/artifacts/homomorphic-image-transfer-obstruction-2026-09-08.md
---

**ESTABLISHED.**  Let `H` be any nontrivial finitely generated group with
`Rad_MF(H) = H`.  Then there is a nontrivial **finitely presented** group `K`
with

```text
Rad_MF(K) = K,                                                        (HIT1)
K = <<t_2, t_3>>,   with t_2, t_3 of order exactly 2 and 3,           (HIT2)
```

so that every nontrivial quotient of `K` contains an element of order exactly
`2` or exactly `3`, every homomorphism from `K` to a torsion-free group is
trivial, and the universal torsion-free quotient of
`torsion-free-universal-quotient-recursively-presented` is

```text
K^tf = 1.                                                             (HIT3)
```

The hypothesis is nonvacuous here: `defect-saturation-full-mf-radical` supplies
a two-generated finitely presented group with full MF radical.

**The obstruction.**  `K` is itself a permitted input -- nontrivial, finitely
presented, full MF radical -- and it has no nontrivial torsion-free quotient at
all.  So there is **no procedure, valid on every input with full MF radical,
which returns a nontrivial torsion-free group as a homomorphic image of its
input.**  Every transfer of that shape fails on `K`.

**Scope.**  This is an obstruction to one class of procedures, not an
impossibility theorem, and in particular:

- it says nothing about **covers**.  A torsion-free `T` surjecting onto `K`
  exists trivially (free groups are torsion-free), which is exactly why
  `free-abelianized-cover-reflects-mf` -- the transfer that runs upward along
  the canonical cover -- is the interesting statement, and it is untouched;
- it does not weaken `torsion-free-mf-radical-routing-saturation`, whose
  hypothesis `(TFR1)` takes the torsion-free quotient `Q` as supplied data.
  What it adds there is that no general procedure can manufacture that `Q` from
  the input;
- it does not contradict the archive's torsion-free theorem.
  `defect-saturation-full-mf-radical` builds a torsion-free full-MF-radical
  group directly, with property `(T)`, rather than transferring one out of an
  arbitrary input; the open target is the property-`(T)`-free version
  `property-t-free-torsion-free-full-mf-radical`.
