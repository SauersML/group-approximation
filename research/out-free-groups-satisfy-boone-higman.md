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
