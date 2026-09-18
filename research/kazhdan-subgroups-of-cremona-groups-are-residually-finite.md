---
rg: 2
id: kazhdan-subgroups-of-cremona-groups-are-residually-finite
kind: claim
title: Every finitely generated Kazhdan subgroup of a Cremona group over any field is residually finite, so no non-residually-finite Kazhdan group is a Cremona host candidate
distinct_from:
  kazhdan-consistent-partial-models-round-to-finite-actions: that is the OPEN quantitative rounding of arbitrary permutation models carrying a consistent set; this proves one exact special case inline (point partial actions of reduced birational maps, which are consistent on every word by the identity principle), with no dependence on that node.
  rational-function-field-crossed-products-have-the-rank-condition: that reduces rational function fields over a prime field modulo p to bound rank defects of skew group rings, and gives soficity of Cremona subgroups; this adds property (T) to the same point model over an arbitrary field and concludes residual finiteness of the group itself.
  kazhdan-subgroups-of-rover-nekrashevych-groups-are-rf: that is the same conclusion for Rover--Nekrashevych hosts via commensurated subsets of a tree boundary; this is for groups of birational transformations via reduction to finite residue fields.
  titz-witzel-kernel-not-elementary-sofic: that rules out elementary sofic permanence for the kernel; this rules out one specific positive host, the Cremona groups, which are sofic by Cornulier.
---

**ESTABLISHED.** Let `k` be any field, `n >= 1`, and let `Gamma <= Bir(P^n_k)`
be a finitely generated group with property (T). Then `Gamma` is residually
finite.

The proof is the route `kazhdan-subgroups-of-cremona-groups-rf-proof`
(requires []). It uses the Nullstellensatz over `Z` (finite residue fields and
the Jacobson property of finitely generated `Z`-algebras) and the definition of
a Kazhdan pair. Everything else is proved there: reduction of the generators
modulo a finite residue field, the partial action on `P^n(F_q)`, its
globalization, the projection onto finite orbits and a Schwartz--Zippel count.

## Consequences

- **No non-residually-finite Kazhdan group embeds in any `Bir(P^n_k)`**, for
  any `n` and any field `k`. That covers every infinite Kazhdan group without
  finite quotients, including every infinite simple Kazhdan group.
- **Titz Mite--Witzel lattices.** By `titz-witzel-simple-kazhdan-cat0-lattices-exist`
  (arXiv:2509.05054v2, Theorem A), each `Gamma_i^q` has property (T) and is
  not residually finite. Its finite residual has finite index, so it also has
  (T). It has no proper finite-index subgroup, and it is infinite, so it is not
  residually finite either. Hence neither `Gamma_1^2` nor the kernel `K` of
  `titz-witzel-kernel-sofic` embeds in any Cremona group. This kills the live
  spark "Cremona host for K" (swarm-0917-w5-pull-tf-2). That spark noted the
  Cantat--Cornulier kill in dimension 2 and left `n >= 3` open. The theorem
  closes every dimension and every field.
- **The invariant and the dying step.** Reduced birational maps compose
  exactly wherever they are regular (the identity principle). So the finite
  point models they give are partial actions that are consistent on *every*
  trivial word, not only on relators. The Kazhdan projection of such a model
  lands on finite orbits of its globalization, and a non-trivial element must
  move almost all of those points. A certificate of soficity that comes from
  an algebraic host whose reductions give exact partial actions (Cremona
  groups, `Aut` of affine spaces, and so on) therefore certifies residual
  finiteness. For `K` it dies at the globalization-plus-projection step.
  Any sofic approximation of `K` must carry inconsistent long-scale monodromy
  on a macroscopic set.

## Scope and novelty

- The literature already has this for complex birational groups. Serge
  Cantat, *Four questions, one partial answer*, poses "Question C": is a
  finitely generated group of birational transformations residually finite?
  Web search on 2026-09-17 reports that Cantat answers yes when the group has
  property (T), and that the general case is open even in dimension 2. The PDF
  (perso.univ-rennes1.fr/serge.cantat/Articles/ahl-web.pdf) now returns HTTP
  403, so its statement and hypotheses were **not read verbatim**, and nothing
  here depends on it. The route is a self-contained proof valid over every
  field, including positive characteristic and finite fields.
- The route proves it for `Bir(P^n_k)`, equivalently `Aut_k(k(x_1..x_n))`.
  For `Bir(V)` of a non-rational variety `V`, the Schwartz--Zippel count has
  to be replaced by the Lang--Weil estimate plus spreading out. That is not
  imported verbatim here, so the extension is not recorded as established.
- Soficity of Cremona groups (Cornulier, arXiv:1305.0993, abstract: "we show
  that Cremona groups are sofic") is untouched. The theorem only says that
  their Kazhdan subgroups gain nothing beyond residual finiteness.
