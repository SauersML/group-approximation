---
rg: 2
id: non-weakly-sofic-finitely-presented-reduction
kind: claim
title: Any non-weakly-sofic group forces a finitely presented one
distinct_from:
  glebsky-rivera-w-sofic-criterion: that is the profinite characterization; this is the corollary of it that eliminates infinitely presented and uncountable candidates from the search
  finitely-presented-sofic-non-mf: that produces a finitely presented group in the MF hierarchy, which is sofic and therefore weakly sofic; this is a reduction principle about the weak-sofic class and produces no group at all
  literal-group-not-sofic: that is a refuted claim about one concrete group `E`, asserting `E` fails soficity, which turned out false; this is an established implication between two existence statements in the weak-sofic class and names no group
  literal-group-sofic: that is soficity of the concrete group `E`, a positive approximation result about one group; this is a reduction principle that transfers a hypothetical failure of weak soficity from an arbitrary group to a finitely presented one
  torsion-free-finitely-presented-non-mf: that is an open existence target for a finitely presented group with an extra algebraic property, in the MF class; this is an established transfer principle in the weak-sofic class, which imposes no torsion condition and asserts no existence
artifacts:
  - research/artifacts/non-weakly-sofic-audit-2026-08-17.md
---

If any group is not weakly sofic, then some **finitely presented** group is
not weakly sofic.  Glebsky--Rivera, J. Algebra **320** (2008), Corollary 4.4.

Two reductions are packed into this, and both matter for how a search is run:

1. **To finitely generated.**  Weak soficity is a local property: a model is
   only a map on a finite set `Phi`, so a model for `Phi` inside the subgroup
   `<Phi>` is a model for `Phi` inside the whole group.  The one subtlety is
   the separation constant, which must be *uniform* across all `Phi`; it is,
   because `alpha` can be normalized to `1` by rescaling the target metric by
   `1/alpha` and asking for multiplicative error `alpha*eps` instead of `eps`
   (Glebsky--Rivera Remark 4.2: the metric is not required to be normalized).
   So if every finitely generated subgroup were weakly sofic, the group would
   be.
2. **To finitely presented.**  Writing the finitely generated culprit as
   `F/N`, the criterion supplies a *finite* list `g_1,...,g_k in N` and an
   `x` in the profinite closure of `[g_1]^F...[g_k]^F` but outside `N`.  Since
   `N(g_1,...,g_k) subseteq N`, the same `x` is outside `N(g_1,...,g_k)`, and
   the closure membership does not mention `N` at all.  So `F/N(g_1,...,g_k)`
   is finitely presented and not weakly sofic.

The second reduction is the one that has teeth: it says the failure was never
about the whole relation subgroup, only about finitely many of its elements.
That is the same "fixed finite list" phenomenon that
`literal-mark-conjugacy-width-unbounded` shows this repository's non-MF
witness cannot supply.
