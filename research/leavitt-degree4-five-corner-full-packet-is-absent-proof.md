---
rg: 2
id: leavitt-degree4-five-corner-full-packet-is-absent-proof
kind: route
title: Pivot every full-packet layout in faithful Bergman normal form
target: leavitt-degree4-five-corner-full-packet-is-absent
requires:
  - leavitt-degree4-strict-omega-four-cycle-no-go
  - degree4-cyclic-orbit-valence-parity
---

The parity and crossing-count theorem forces length twelve for two unary and
two equal five-corner orbits.  A topology enumeration gives six dihedral sign
classes; exactly the two displayed in the target have corner-length profile
`(1,1,1,1,8)` in both residual orbits.  These are the minimal non-strict
classes in which four separated singleton carriers can cancel around a long
composite corner.

The attached program enumerates all `12P7` injections of the seven distinct
packet coefficients for each topology.  For each layout and each of the two
unary pivots it:

1. solves the pivot relator exactly for `z=t^4`;
2. substitutes that faithful Bergman normal form into the other unary word;
3. rejects unless the other unary relation is exactly the identity;
4. only then substitutes into both ordered five-corner residuals and compares
   their cyclically reduced quotient with `Omega(c,p)` and its inverse.

MSI array job `16662164` split the placements into 128 congruence shards.
Exactly 128 terminal output files were returned.  Every file reports

```text
ordered_candidates_tested 0
hits 0
```

so stage 3 rejects all `15,966,720` layout/pivot choices.  In particular the
marked target stage has no candidate on which it could succeed.
