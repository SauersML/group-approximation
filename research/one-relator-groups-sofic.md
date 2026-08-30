---
rg: 2
id: one-relator-groups-sofic
kind: claim
title: "Pestov Question 4.10: every one-relator group is sofic"
root: true
distinct_from:
  nonsofic-one-relator-group: that is the negative answer to the same question and asks for a witness; this is the affirmative answer and asks for a proof covering all relators. They cannot both be established, and no route to either is a route to the other.
  residually-rationally-solvable-one-relator-sofic: that is this statement restricted to the residually rationally solvable subclass, and it is closed; this is the full question and is open.
  hyperlinear-implies-sofic: that is Pestov's Question 3.4 in the affirmative and concerns hyperlinear groups; this is his Question 4.10 and concerns one-relator presentations. Neither is known to bear on the other.
  pestov-question-5-3-negative: that is Pestov's Question 5.3, about essentially free near actions, and it is closed negatively by this development; this is his Question 4.10 and is untouched by it.
  q3-4-resolved: that is the program goal — Pestov's Question 3.4, resolved either way, about hyperlinear groups — and admits exactly two answer routes by construction; this is his Question 4.10, a single directional statement about one-relator groups, with ordinary routes and a separate negation claim. Neither question is known to bear on the other.
  one-relator-fox-magnus-descent-to-derived-linton-radical: that proves every one-relator group sofic only after quotienting by the derived Linton radical and gives a new positive class when `R' = 1`; this asks for the remaining nonabelian core as well.
artifacts:
  - research/artifacts/one-relator-soficity-audit-2026-08-17.md
---

OPEN.  Pestov, *Hyperlinear and sofic groups: a brief guide* (arXiv:0804.3968),
Open Question 4.10: is every one-relator group `G = <X | w>` sofic?

Two live routes and two dead ones are recorded below.  As of 2026-08-17 the
question is unresolved in both directions; the negative answer is the separate
claim [[nonsofic-one-relator-group]].

## What is already settled

- [[one-relator-soficity-is-torsion-free-two-generator-case]] — the full
  question is exactly equivalent to the torsion-free two-generator case.
  Torsion one-relator groups are residually finite, and every torsion-free
  one-relator group embeds in a torsion-free two-generator one-relator group.
- [[residually-rationally-solvable-one-relator-sofic]] — the whole residually
  rationally solvable subclass is sofic.
- [[one-relator-soficity-localizes-at-rational-derived-stage]] — for every
  one-relator group there is an `n <= |w|` with `G` sofic **iff** `E = G_Q^(n)`
  sofic, and `E` is free-by-(rationally perfect).  So the remaining content of
  this claim is exactly [[linton-shell-sofic]].
- [[one-relator-fox-magnus-descent-to-derived-linton-radical]] — the whole
  quotient `G/R'` embeds in a finite-lamp wreath product and is sofic, while
  `E/R'` is residually finite.  In particular
  [[one-relator-abelian-linton-radical-sofic]] closes the class `R' = 1`.
- [[nonsofic-one-relator-relator-has-primitivity-rank-two]] — any
  counterexample has `π(w) = 2`, so is torsion-free and locally indicable.

## Attempts

1. **Reduce to the Linton shell and prove the shell sofic.**  *Live, with its
   first-order layer closed*, recorded
   as `one-relator-sofic-via-linton-shell`.  The reduction is done; the shell is
   [[linton-shell-sofic]].  Its quotient by `R'` is residually finite; all
   remaining difficulty sits in an action-compatible, genuinely nonabelian
   approximation of the derived core.
2. **Magnus induction on relator length.**  *Stalls, and the stall is precise.*
   For `χ : G ↠ Z` with `t`-exponent-sum zero, `ker χ` is a bi-infinite amalgam
   of shorter one-relator pieces `B_i` over free Magnus subgroups `C_i`, and
   `G` is sofic iff `ker χ` is (the quotient is `Z`, amenable).  When
   `rank C_i <= 1` the edge groups are amenable and existing amalgamation
   permanence plus directed unions finish.  When `rank C_i >= 2` the edge group
   is a nonamenable free group and no permanence theorem applies; worse, a
   finite window of the chain is a **staggered multi-relator** group, not a
   smaller one-relator group, so the induction hypothesis is not available
   either.  The repair is isolated as [[magnus-staggered-chain-sofic]] and
   routed by `one-relator-sofic-via-magnus-staggered-amalgam`.
3. **Recent graph-of-groups soficity theorems.**  *Dies on hypothesis
   mismatch.*  Gao--Kunnawalkam Elayavalli--Mj (arXiv:2408.11724) cover doubles
   and graphs whose edge embeddings are identical or separability-controlled; a
   generic Magnus HNN has **two distinct** embeddings of its free associated
   subgroup, and nothing in the theorem identifies them.
4. **Sofic kernel with residually amenable quotient.**  *Dead*, recorded as
   `one-relator-sofic-via-residually-amenable-quotient` and killed by
   [[relative-soficity-extension-theorem-withdrawn]].  This is the most
   attractive wrong turn in the region — Linton hands over a residually
   rationally solvable quotient on a plate — so it is labelled rather than
   omitted.
5. **Semidirect closure applied to the shell.**  *Dead*, recorded as
   `linton-shell-sofic-via-generic-semidirect-closure` and killed by
   [[sofic-semidirect-product-closure-fails]].
6. **Strong Atiyah / Lück approximation / coherence.**  *Discarded, not
   attempted to conclusion.*  The recent one-relator literature is rich in
   approximation theorems, none of which states or implies soficity; an
   operator-algebraic or homological approximation is not an approximation by
   symmetric groups, and treating a similarly-named theorem as a bridge would
   be exactly the error this graph exists to prevent.

First-order Fox, abelian, solvable, and rational-derived iterations are no
longer live completion strategies in the perfect-core regime.  Their maximal
descent is the exact kernel `R'` computed above; when `k = 1`, `R = R'` is
already perfect and every solvable lamp quotient is trivial.
