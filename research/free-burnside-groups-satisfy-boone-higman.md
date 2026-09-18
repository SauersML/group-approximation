---
rg: 2
id: free-burnside-groups-satisfy-boone-higman
kind: claim
title: Every infinite free Burnside group with solvable word problem embeds in a finitely presented simple group
distinct_from:
  free-burnside-is-a-limit-of-hyperbolic-groups: that is the literature input that B(m,N) is a direct limit of hyperbolic quotients of F_m; each stage embeds in a finitely presented simple group, but limits are not preserved, and this asks for one simple finitely presented host of the limit itself.
  free-burnside-large-odd-exponent-is-nonamenable: that records non-amenability, hence infiniteness, of B(m,N) for large odd N; this is the Boone--Higman embedding question for those groups.
  hyperbolic-groups-satisfy-boone-higman: that covers hyperbolic inputs; an infinite free Burnside group is not a subgroup of any hyperbolic group, because torsion subgroups of hyperbolic groups are finite.
artifacts:
  - research/artifacts/gq-bh-bh-testcases-ranking.md
---

**OPEN.** Let `m >= 2`, and let `n` be an exponent for which the free Burnside
group `B(m,n) = F_m / <<w^n : w in F_m>>` is infinite with solvable word problem.
Then `B(m,n)` embeds in a finitely presented simple group.

This is item (6) of Problem 5.3 of Belk--Bleak--Matucci--Zaremsky,
arXiv:2306.16356v3 ("Free Burnside groups B(m,n) with solvable word problem"),
quoted in `research/artifacts/bh-survey-open-cases-status-2026-09-12.md` §1.
Remark 5.4 there records no progress on item (6). Before this node the graph had
no Boone--Higman node for it (`research/artifacts/gq-bh-bh-map-subgraph.md`, §4
item 1).

**Which exponents.** Lane-level literature recall, not pinned at source here:
- odd `n >= 665` (Novikov--Adian; Adian's monograph), where `B(m,n)` is infinite
  and has solvable word problem;
- large even `n` (Ivanov; Lysenok), under their divisibility hypotheses.
The single test case `B(2,665)` would be enough for `m = 2`. A reduction of all
`m` to `m = 2` via Širvanjan's embedding `B(m,n) <= B(2,n)` is recalled in
`research/artifacts/ideas-bh-round2-2026-09-14.md` item 8, and is unpinned.

## Hosts that cannot work (reasons are textbook, not pinned here)

- **Linear hosts.** A finitely generated periodic linear group is finite
  (Burnside--Schur). So `B(m,n)` is linear over no field, and none of the linear
  Boone--Higman classes on main reach it
  (`finitely-generated-linear-groups-satisfy-boone-higman`).
- **Residually finite and self-similar hosts.** By Zelmanov's solution of the
  restricted Burnside problem, a finitely generated residually finite group of
  exponent `n` is finite. So an infinite `B(m,n)` is not residually finite, and it
  embeds in no residually finite group. That includes every group acting
  faithfully on a locally finite rooted tree
  (`self-similar-hosts-contain-only-residually-finite-groups`), and every f.p.
  self-similar host.
- **Hyperbolic hosts.** Torsion subgroups of hyperbolic groups are finite, so no
  hyperbolic group contains an infinite `B(m,n)`. The hyperbolic approximations
  `G_k -> B(m,n)` of `free-burnside-is-a-limit-of-hyperbolic-groups` each satisfy
  Boone--Higman (`hyperbolic-groups-satisfy-boone-higman`), but only as quotients,
  which gives nothing for the limit.
- **Cubulated hosts.** Groups acting properly on finite-dimensional CAT(0) cube
  complexes have no infinite torsion subgroups (Sageev--Wise), so those hosts are
  dead too. For general CAT(0) groups the analogous statement is itself open, so
  `cat0-groups-satisfy-boone-higman` is not known to exclude or include anything
  here.

- **Almost automorphism hosts, including V and every Röver–Nekrashevych group.**
  `almost-automorphism-torsion-subgroups-are-rf` (lane proof, bh-free-12) shows that every finitely generated
  torsion subgroup of the almost automorphism group `𝒩_d` of the rooted d-ary tree is residually finite. So by
  Zelmanov no infinite `B(m,n)` embeds in `𝒩_d`. That excludes the finitely presented simple hosts themselves, not
  only the self-similar overgroups:
  - `V` and all Higman–Thompson groups `V_d` (for `V` this is Röver's torsion local finiteness);
  - every Röver–Nekrashevych group `V_d(G)`, for every self-similar `G`, including Röver's group, the hosts of
    Zaremsky's Thm 1.1 and the contracting hosts of Belk–Matucci.

## What torsion does NOT rule out

Periodicity is not an obstruction by itself. Röver's finitely presented simple
group `V(G)` contains Grigorchuk's infinite 2-group
(`research/artifacts/ideas-2026-09-13/bh/bh-obstruction.md`, approach 3). The
difference is that Grigorchuk's group is residually finite and acts on a rooted
tree, while `B(m,n)` does not. So a host has to realize an infinite periodic group
of bounded exponent without any rooted-tree action, which no construction on main
does.

## Attempts

Candidate levers recorded when the node was opened:
- a type (A) or twisted Brin--Thompson actor containing `B(m,n)`: first question,
  does `B(m,n)` have any faithful action with finitely many orbits on pairs;
- a single finitely presented simple host for the whole directed system of
  hyperbolic quotients `G_k` (e.g. one BBMZ-type germ extension that works
  uniformly in `k` and survives the limit);
- a refutation direction: any property of finitely presented simple groups that
  is inherited by subgroups and fails for infinite bounded-exponent groups.

1. **Attempt 1 (2026-09-18, lane `bh-bbmz-problems`): the actor must be a finitely
   presented overgroup; no candidate found.** It corrects the first lever above.
   - `B(m,n)` itself can never be the actor. By FWZ arXiv:2603.24687 Theorem B (as
     imported in `abstract-btb-pairs-fp-and-relatively-simple-citation`), `SV_G` is
     finitely presented iff `G ↷ S` has type `[A_2]`. Type `[A_2]` requires `G` to be
     finitely presented, and `B(m,n)` is not. So the right first question is whether
     some finitely presented overgroup `P ⊇ B(2,n)` admits a type (A) action, i.e.
     whether `B(2,n) ∈ B_A`.
   - Any such `P` fails to be residually finite (Zelmanov, above), is not hyperbolic
     and is not cubulated. So none of the actors on main qualifies: linear,
     self-similar, and cube-complex actors are all out.
   - Clapham's finitely presented overgroups with solvable word problem come with no
     action.
   - No candidate `P` was found. Stalled here, with the precise open gate:
     `B(2,n) ∈ B_A`.
2. **Attempt 2 (2026-09-18, lane `bh-free-12`): the Röver–Nekrashevych world is closed; the host question is
   isolated.**
   - Proved `almost-automorphism-torsion-subgroups-are-rf`. The argument uses a depth cocycle, which vanishes at
     fixed points of torsion elements; a pushdown pumping bound; and finite permutation quotients on deep cones. So
     every finitely presented simple group built as a Röver–Nekrashevych group, and `V` itself, is excluded as a
     host. The periodic Grigorchuk subgroup of Röver's `V(G)` noted above is consistent with this: it is residually
     finite, of unbounded exponent.
   - The argument fails for Brin–Thompson `nV`, `n >= 2`. There the depth cocycle is a vector, and the pumping step
     breaks. So `nV` and twisted Brin–Thompson groups remain the natural finitely presented simple candidates.
   - The first necessary step is the separate claim
     `some-fp-simple-group-has-an-infinite-bounded-exponent-subgroup` (bh-free-06; the duplicate
     `fp-simple-groups-can-contain-infinite-finite-exponent-groups` points to it): does some finitely presented
     simple group contain an infinite finitely generated group of finite exponent? BH implies it, via `B(2,665)`, and
     a negative answer would refute BH.
   - Also excluded: finitely presented simple Kac–Moody lattices with 2-dimensional buildings, e.g. `Λ_(2,4,6)(q)`,
     and every group acting with finite point stabilizers on a finite product of 2-dimensional CAT(0) triangle
     complexes and trees (`two-dim-cat0-product-groups-are-torsion-locally-finite`, from Norin–Osajda–Przytycki).
     Kac–Moody lattices with Weyl group containing no `Z^2` (word-hyperbolic `W`, any building dimension) are
     excluded too (`hyperbolic-kac-moody-lattices-are-torsion-locally-finite`, from Haettel–Osajda and
     Caprace–Haglund). Open: Kac–Moody lattices with `Z^2 ≤ W` and a spherical triple.
