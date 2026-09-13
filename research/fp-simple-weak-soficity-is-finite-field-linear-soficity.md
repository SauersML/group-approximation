---
rg: 2
id: fp-simple-weak-soficity-is-finite-field-linear-soficity
kind: claim
title: A finitely presented infinite simple group is weakly sofic iff it is linear sofic over finite fields, and otherwise has bounded relator width over all finite groups
distinct_from:
  simple-group-width-over-all-finite-simple-groups: that is the dichotomy over finite simple targets only; this is the same dichotomy over every finite group, so it identifies weak soficity itself.
  relator-width-bounded-by-almost-simple-quotients: that reduces every finite target to its quotient by G_0 and bounds the width when almost simple quotients are bounded; this handles large almost simple quotients by moving the tuple into the socle.
  fg-simple-weakly-sofic-groups-are-sofic: that is the open rigidity claim; this reduces its finitely presented case to linear soficity over finite fields.
---

**ESTABLISHED (unreviewed)** by `fp-simple-weak-soficity-is-finite-field-linear-soficity-proof`.

Let `G = <X | R>` be an infinite finitely presented simple group. "Linear sofic over finite fields" is as defined on
`simple-group-psl-width-is-finite-field-linear-soficity`: `G` embeds in a rank-metric ultraproduct of groups
`GL_(n_i)(F_(q_i))`. The following are equivalent:
- (i) `G` is not linear sofic over finite fields;
- (ii) there is `K(G)` with `w_Q(a) <= K(G)` for **every** finite group `Q` and every `a in Q^X`, with conjugators in `Q`;
- (iii) `G` is not weakly sofic.

**In words.** For finitely presented simple groups, weak soficity is exactly linear soficity over finite fields.
Non-simple finite targets add nothing: soluble layers, wreath towers, congruence kernels and twisted products all
reduce to direct products of finite simple groups.

**Dependencies (all unreviewed except the imports).**
- `relator-width-bounded-by-almost-simple-quotients`, resting on Nikolov--Segal (`nikolov-segal-generation-by-conjugates`).
- `simple-group-relator-templates-over-finite-simple-groups`, and through it the classical covering theorems of lane
  `ex-weak-sofic-classical-covering`.
- The strong Schreier conjecture (outer automorphism groups of finite simple groups are soluble of derived length
  `<= 3`), a consequence of the classification, as recorded in Nikolov--Segal arXiv:1102.3037v6, page 2.

**Consequences.**
- **Rigidity.** For finitely presented groups, `fg-simple-weakly-sofic-groups-are-sofic` is equivalent to: *every
  finitely presented simple group that is linear sofic over finite fields is sofic*. Kind (b) on that node, weak models
  only through non-simple targets, is empty.
- **Non-weakly-sofic groups.** An infinite finitely presented simple group that is not linear sofic over finite fields
  is not weakly sofic, so it would answer Glebsky--Rivera Conjecture 4.5 (`non-weakly-sofic-group-exists`).
- **The binary Leavitt unit group.** `R^x` is weakly sofic iff it is linear sofic over finite fields. So
  `binary-leavitt-unit-group-is-weakly-sofic` is equivalent to this linear-sofic statement, and the Gottschalk gate
  `binary-leavitt-unit-group-is-f2-linear-sofic` would imply it.

**Model test.**
- *Trivial model.* A sofic simple group fails (i), is weakly sofic, and has unbounded width over `Sym(n)`, as required.
- *Real object.* No finitely presented simple group is known to satisfy (i), because no group is known to be
  non-linear-sofic. So (i) => (iii) is a reduction, not a non-weak-soficity proof for a known group.
- *Hypothesis check.* Finite presentation is used for the width formulation, and simplicity for "no finite quotients".
  Simplicity is also used in the dichotomy for simple targets. Finitely presented groups without finite quotients
  that are not simple are not covered by (iii) => (i).

**Credit.** The group-theoretic reduction is due to Nikolov, Schneider and Thom. By their Theorem 4
(`nst-simple-weakly-sofic-groups-are-psl-approximable`), every simple weakly sofic group is approximable by the groups
`PSL_n(q)` with invariant lengths. Combined with the PSL dichotomy of `simple-group-psl-width-is-finite-field-linear-soficity`
(lane `ex-weak-sofic-classical-covering`, unreviewed), this gives (iii) => (i) directly; see route
`fp-simple-weak-soficity-via-nst-psl-approximation`. So the new content is the combination with that PSL
dichotomy, which identifies the target property as linear soficity over finite fields. The width-form proof in
`fp-simple-weak-soficity-is-finite-field-linear-soficity-proof` is a second, independent route through the finite-simple
templates. Arzhantseva--Paunescu were not re-read for a stated converse. The check covered the Nikolov--Schneider--Thom
abstract and Theorems 1 and 4 only.
