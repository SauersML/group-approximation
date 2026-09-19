---
rg: 2
id: property-t-free-seed-via-intrinsic-seed
kind: route
title: Read the minimal torsion-free seed off the intrinsic acylindrical seed
target: property-t-free-torsion-free-fp-non-mf-seed
requires:
  - torsion-free-fp-ah-mf-radical-seed
  - universal-mf-quotient
---

**Proof.**  Let `(E,d)` be supplied by `torsion-free-fp-ah-mf-radical-seed`.
Then `E` is finitely presented and torsion-free, `d != 1`, and
`d in Rad_MF(E)`.  The proof of `(TFS1)` is required to avoid Property `(T)`,
Kazhdan subgroups, projections and transport, and every seed with such a
dependency.  By `universal-mf-quotient`, `E -> E/Rad_MF(E)` is the universal
MF quotient.  So `E` is MF iff `Rad_MF(E)=1`.  Since `d != 1` lies in the
radical, `E` is not MF.  This is exactly `property-t-free-torsion-free-fp-non-mf-seed`,
and its proof inherits the no-`(T)` clause.  The acylindrical-hyperbolicity
clause of `(TFS1)` is discarded.

**What this route changes.**  Before this route, the only route that fed
`torsion-free-fp-ah-mf-radical-seed` toward the goal was
`property-t-free-torsion-free-via-intrinsic-seed`.  That route also requires
the open `internal-torsion-free-single-word-router`.  Composed with
`property-t-free-torsion-free-via-embedding-router`, this route does not need
it.  The other four requirements of the embedding
router are established:

- `universal-mf-quotient`;
- `torsion-free-embedding-normal-generation-router`;
- `two-generated-acylindrical-normal-generation-upgrade`;
- `mf-radical-saturation-along-any-homomorphism`.

So the torsion-free leg (endpoint 6) of `property-t-free-manuscript-results`
now has two independent open cones:

```text
(A) property-t-free-leavitt-full-mf-radical + full-mf-radical-abelianized-cover-is-not-mf
(B) torsion-free-fp-ah-mf-radical-seed
      <= torsion-free-mf-seed-via-higman-four-cycle
      <= higman-four-cycle-intrinsic-mf-seed
      <= bs12-trivially-padded-opnorm-correction + higman-exact-packet-cycles-collapse-opnorm
```

Cone (B) shares no node with the Leavitt collapse.  The two prerequisites of
(B), `(TPC)` and `(CGC)`, can each fail on their own.  Neither mentions
routing, torsion or finite presentation.  Every group-theoretic clause is
handled by established nodes.
