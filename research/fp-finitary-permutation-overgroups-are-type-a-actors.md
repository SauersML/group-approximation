---
rg: 2
id: fp-finitary-permutation-overgroups-are-type-a-actors
kind: claim
title: A finitely presented permutation group containing all finitary alternating permutations acts with type (A)
distinct_from:
  fp-simple-highly-transitive-groups-satisfy-pbh: that turns a finitely presented SIMPLE highly transitive group into a type (A) actor through the BFFHZ automorphism construction; this needs no simplicity, uses the natural action itself, and the groups here are never simple, since Alt_fin(X) is a proper normal subgroup.
  fp-full-binary-cantor-groups-have-type-a-actions: that gets type (A) on clopens from a copy of standard V; this gets it on points from a copy of Alt_fin(X), with no Cantor structure.
  lampshuffler-groups-are-not-fp2-over-q: that kills the split extensions FSym(X) x| Gamma over free Gamma-sets; this shows every finitely presented overgroup of Alt_fin(X), split or not, is automatically a type (A) actor, so finite presentation is the only condition left.
  every-countable-group-lies-in-a-faithful-ha2-actor: that notes groups containing FSym(S) have one orbit of pairs and finds lampshuffler stabilizers finitely generated; this proves stabilizers are finitely generated for every finitely generated overgroup.
---

**ESTABLISHED** through `fp-finitary-permutation-overgroups-type-a-proof`.
Elementary; not independently reviewed; no novelty claimed.

## Statement

Let `X` be a countably infinite set and let `Gamma <= Sym(X)` be finitely
generated with `Alt_fin(X) <= Gamma`. Write `N = Gamma ∩ FSym(X)` and
`Q = Gamma / N`.

1. **Pairs.** The action of `Gamma` on `X` is faithful and highly transitive. It
   has exactly two orbits on ordered pairs and one on two-element subsets.
2. **Stabilizers.** Every point stabilizer `Gamma_x` is finitely generated.
3. **Type (A).** So the action `Gamma ↷ X` is of type (A) exactly when `Gamma`
   is finitely presented. In that case every subgroup of `Gamma` embeds in the
   finitely presented simple group `SV_Gamma`
   (`type-a-action-gives-boone-higman-for-subgroups`), and satisfies
   permutational Boone--Higman.
4. **Quotient.** `N` is `Alt_fin(X)` or `FSym(X)` and is the normal closure in
   `Gamma` of at most two elements. So if `Gamma` is finitely presented, `Q` is
   finitely presented.
5. **Subgroups.** For every subgroup `H <= Gamma`, `H ∩ N` is a locally finite
   normal subgroup of `H` and `H / (H ∩ N)` embeds in `Q`. In particular a
   group with no nontrivial locally finite normal subgroup embeds in `Gamma`
   only if it embeds in `Q`.

## Consequences

- **Finite presentation is the whole problem.** For overgroups of
  `Alt_fin(X)`, faithfulness, the pair count and stabilizer generation all hold
  automatically. The universality question
  `decidable-groups-embed-in-fp-finitary-overgroups` asks only for finite
  presentation.
- **No free lunch from the finitary layer.** By item 5, a finitary overgroup
  embeds an input with trivial locally finite radical only through its
  finitely presented quotient `Q`. Every obstruction to a host class that
  passes to quotients by locally finite normal subgroups therefore transfers
  to finitary extensions of that class. An example is an infinite Kazhdan input
  with finite locally finite radical such as Deligne's lattice. So the
  finitary layer cannot rescue a dead host class for such inputs. It only
  supplies the type (A) action.
- **Examples, not load-bearing, citations not re-read here.** Houghton's
  groups `H_n` for `n >= 3` are finitely presented (Brown, JPAA 44, 1987), and
  so is Lehnert's quasi-automorphism group `QV` of the binary tree
  (Nucinkis--St. John-Green). Both contain `FSym` of their natural set, so by
  item 3 their natural actions are of type (A).
