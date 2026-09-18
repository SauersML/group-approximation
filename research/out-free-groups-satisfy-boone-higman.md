---
rg: 2
id: out-free-groups-satisfy-boone-higman
kind: claim
root: true
title: Every Out(F_n) with n at least three embeds in a finitely presented simple group
distinct_from:
  aut-free-groups-satisfy-permutational-boone-higman: that is the known theorem for Aut(F_n); this is the open outer case, where the inner automorphisms are quotiented out and the BFFHZ action no longer applies.
  boone-higman-conjecture: that quantifies over all finitely generated groups with solvable word problem; this is the special case Out(F_n), the part of item (3) of the survey's Problem 5.3 still open after BFFHZ.
  closed-surface-mapping-class-groups-satisfy-boone-higman: that is the closed-surface mapping class group case, item (2); this is Out(F_n), item (3). BFFHZ expect a method for this case to also give that one.
artifacts:
  - research/artifacts/bh-out-fn-closed-mcg-2026-09-12.md
---

**OPEN.** For every `n ≥ 3`, `Out(F_n)` embeds in a finitely presented simple
group.

This is the open part of a named problem.
- **Survey.** Belk--Bleak--Matucci--Zaremsky, arXiv:2306.16356v3, Problem
  5.3(3), "The groups Aut(Fn) and Out(Fn)", and Remark 5.4: "item (3) remains
  open for Out(Fn) for all n ≥ 3".
- **Known.** `Aut(F_n)` is done by BFFHZ Theorem A
  (`aut-free-groups-satisfy-permutational-boone-higman`).
- **Small rank.** `Out(F_2) ≅ GL_2(Z)` is a finitely generated subgroup of
  `GL_2(Q)`, covered by Zaremsky arXiv:2405.09722 Theorem 1.2.

## Attempts

1. **A type (A) action of Out(F_n) itself.** BFFHZ, arXiv:2503.21882v2,
   Remark 2.5.
   - **Garion--Glasner.** Out(F_n) acts highly transitively on `n`-generator
     presentations modulo `Aut(G)`, but "for a very special choice of G: a
     lawless Tarski monster", for which "no finitely presented example is
     known". So "it is unclear whether the stabilizers of such actions can ever
     be finitely generated".
   - **Hull--Osin.** The highly transitive actions of acylindrically
     hyperbolic groups are "built using small cancellation techniques, and so it
     is even less likely that the methods could lead to a type (A) action for
     Out(Fn)".
2. **An analogue of Aut_G(G∗F_n).** BFFHZ Section 4: "inner automorphisms of Fn
   do not interact nicely with G-automorphisms, so it is not clear whether this
   is possible."
   - **Why, concretely.** In `Aut_G(G∗F_n)` acting on `Hom_G(G∗F_n, G) ≅ G^n`,
     an inner automorphism of `F_n` extended by the identity on `G` moves a
     tuple by conjugation by the value of the conjugator.
   - **What breaks.** The quotient by diagonal conjugation is invariant only
     under automorphisms whose words carry no constants from `G`. Those are
     just `Aut(F_n)`, so the transitivity that `G` supplies is lost.
3. **Virtual embedding in Aut(F_m).** Route `out-fn-bh-via-virtual-embedding-in-aut-fn`,
   with open premise `out-free-groups-virtually-embed-in-aut-free-groups`. Every
   construction by lifting to a finite-index subgroup of `F_n` is a virtual
   section of `Aut(F_n) → Out(F_n)` (`outer-covering-lifts-are-virtual-sections`).
4. **Necessary condition on a direct type (A) actor** (bh-free-40,
   `out-free-pair-finite-stabilizers-contain-fully-irreducibles`; lane proof).
   - **The condition.** In any action of `Out(F_n)` with finitely many pair
     orbits, the stabilizer `H` of a point with infinite orbit has these
     properties:
     - unbounded orbits on the free factor complex;
     - it contains fully irreducibles (Handel–Mosher);
     - no finite-index subgroup fixes a proper free factor class;
     - it is not commensurated.
   - **What it excludes.** Every geometric stabilizer: free factors, free factor
     systems, free splittings, non-filling conjugacy classes, and points of
     Outer space.
   - **Relation to BLIW.** Commensurator rigidity, which kills BLIW Theorem C
     here (`commensurator-rigid-groups-have-no-faithful-bs-members`), does not
     touch this route, since type (A) stabilizers are never commensurated.
   - **Next test.** The stabilizer of the conjugacy class of a filling element,
     e.g. a one-boundary surface word: does it have finitely many double
     cosets?
5. **Surface-word stabilizers fail too** (bh-free-40,
   `surface-word-stabilizers-have-infinitely-many-double-cosets`; lane proof,
   cites Dehn–Nielsen–Baer and Mirzakhani's orbit count).
   - **The result.** For `n = 2g ≥ 4`, the stabilizer of the one-cusp surface
     word has infinitely many double cosets. So does every subgroup virtually
     contained in it.
   - **Why.** Its `Aut`-orbit grows exponentially, via the transvections
     `a_1 ↦ a_1 c`, while mapping-class-group orbits grow polynomially.
   - **Where that leaves Attempt 4.** A direct type (A) stabilizer must also
     avoid this last natural geometric shape.
