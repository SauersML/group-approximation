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
- **Binary Leavitt unit group.** `R^x` has weak models into finite simple groups iff it is linear sofic
  over finite fields. In characteristic `2` this is the Gottschalk gate
  `binary-leavitt-unit-group-is-f2-linear-sofic`. If `R^x` is not linear sofic over finite fields,
  every weak model of `R^x` uses non-simple targets of the kind above.

Derivation: `simple-group-width-over-all-finite-simple-groups-proof`.
