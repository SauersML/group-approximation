---
rg: 2
id: property-t-free-seed-via-virtual-torsion-corner
kind: route
title: Place a no-CE corner on a finite subgroup of a virtually torsion-free host and trace it down
target: property-t-free-torsion-free-fp-non-mf-seed
requires:
  - virtually-torsion-free-host-no-ce-augmentation-corner
  - nonhyperlinear-finite-augmentation-corner-kills-mf
  - virtually-torsion-free-infinite-mf-radical-gives-seed
artifacts:
  - research/virtually-torsion-free-infinite-mf-radical-gives-seed-proof.md
---

**What this route changes.**  Until now the seed had one route,
`property-t-free-seed-via-leavitt-abelianized-cover`.  That route needs both
the Leavitt collapse and the abelianized-cover descent hole
`full-mf-radical-abelianized-cover-is-not-mf`, which has been attacked in six
waves without success.  This route needs neither.  Its prerequisites fail
independently:

- the lemma `virtually-torsion-free-infinite-mf-radical-gives-seed` is
  established;
- the corner theorem is established;
- the single hole is a host-construction problem.

The obstruction `torsion-free-seeds-need-kernel-descent-or-trace-corner`
shows that every radical-calculus route to the seed passes through one of two
gates.  The abelianized-cover route uses the descent gate; this route is the
other gate.

**Distinct from** `property-t-free-seed-via-leavitt-abelianized-cover`: no
quotient, no cover and no descent step appear, and the binary-Leavitt input
is not used.

## Steps

1. The hole supplies `H`, `E`, `K` and `Phi : B -> q_K C[H] q_K`.
2. `nonhyperlinear-finite-augmentation-corner-kills-mf` gives
   `K <= Rad_MF(H)`.
3. `K` is not contained in `W(H)`, so `Rad_MF(H)` is not contained in
   `W(H)`.
4. Case 2 of `virtually-torsion-free-infinite-mf-radical-gives-seed` gives a
   finitely presented torsion-free non-MF `T` containing `E`.

## Property-T audit

Each of the three prerequisites is audited free of Kazhdan input.  The hole
forbids it by statement.
