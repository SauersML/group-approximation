---
rg: 2
id: simple-group-width-over-all-finite-simple-groups
kind: claim
title: A finitely presented simple group has bounded relator width over all finite simple groups iff it is not linear sofic over finite fields
distinct_from:
  simple-group-relator-width-in-finite-simple-targets: that bounds width over symmetric, alternating, sporadic and bounded-rank targets for nonsofic groups; this assembles every finite simple group and identifies the exact hypothesis.
  simple-group-psl-width-is-finite-field-linear-soficity: that is the special linear family with its converse; this is the statement over every finite simple group at once.
  fg-simple-weakly-sofic-groups-are-sofic: that is the open rigidity statement over all finite groups; this settles the finite simple targets, where it becomes a question about linear soficity over finite fields.
---

**ESTABLISHED (unreviewed).** Let `G = <X | R>` be an infinite finitely presented simple group. The
following are equivalent:
- (i) `G` is not linear sofic over finite fields, meaning it embeds in no rank-metric ultraproduct of
  `GL_(n_i)(F_(q_i))`;
- (ii) there is `K = K(G)` with `w_Q(a) <= K` for every finite simple group `Q` and every `a in Q^X`;
- (iii) `G` has no sequence of weak models into finite simple groups with bi-invariant lengths.

**In words.** For finitely presented simple groups, weak soficity through finite simple groups is
exactly linear soficity over finite fields. Symmetric, sporadic and exceptional targets add nothing
beyond it, and neither do classical targets of any type or rank.

**Model test and scope.**
- *Trivial model.* A sofic group fails (i) and has unbounded width over `PSL_n(q)`, as it should.
- *Real object.* No finitely presented simple group is known to satisfy (i). No group at all is known
  to be non-linear-sofic (`non-linear-sofic-group` is open), and whether `R^x` is `F_2`-linear sofic is
  the open Gottschalk gate.
- *So the forward direction is a reduction.* It is not a width bound for a known group. The direction
  (iii) => (i) is unconditional: any weak model of a finitely presented simple group into finite simple
  groups yields linear soficity over finite fields.

**Consequences.**
- **Restricted rigidity.** Restricted to finite simple targets, `fg-simple-weakly-sofic-groups-are-sofic`
  for finitely presented groups is: *every finitely presented simple group that is linear sofic over
  finite fields is sofic*. This is a finite-field, simple-group case of Arzhantseva--Paunescu Question 8.5
  (`linear-sofic-nonsofic-group`).
- **Where a counterexample can live.** A finitely presented simple weakly sofic nonsofic group must do
  one of two things:
  - be linear sofic over finite fields, which is then a linear-sofic nonsofic group, a strictly
    stronger object; or
  - have weak models whose targets eventually leave every class with bounded width. That class
    contains the finite simple groups, the nilpotent groups
    (`perfect-group-relator-width-over-nilpotent-groups`), and products and bounded extensions of
    these by the template trick. This is the non-simple room of Glebsky's extension proofs, with deep
    iterated wreath products as the model case (lane `ex-weak-sofic-deep-wreath`).

  **The second option is empty (2026-09-13, lane `ex2-weak-sofic-bounded-factors`, unreviewed).** By
  `fp-simple-weak-soficity-is-finite-field-linear-soficity`, a finitely presented simple group that is not linear
  sofic over finite fields has bounded width over every finite group. There are two routes. One is
  Nikolov--Schneider--Thom Theorem 4 (`nst-simple-weakly-sofic-groups-are-psl-approximable`) with this node's PSL
  case. The other reduces to `Q/Q_0` (`relator-width-bounded-by-almost-simple-quotients`) and applies the finite-simple
  templates in the socle. So only the first option remains.
- **Binary Leavitt unit group.** `R^x` has weak models into finite simple groups iff it is linear sofic
  over finite fields. In characteristic `2` this is the Gottschalk gate
  `binary-leavitt-unit-group-is-f2-linear-sofic`. If `R^x` is not linear sofic over finite fields, it has no weak
  models at all, so it is not weakly sofic (`fp-simple-weak-soficity-is-finite-field-linear-soficity`).

Derivation: `simple-group-width-over-all-finite-simple-groups-proof`.
