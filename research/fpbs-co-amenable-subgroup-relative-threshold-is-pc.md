---
rg: 2
id: fpbs-co-amenable-subgroup-relative-threshold-is-pc
kind: claim
title: Every co-amenable subgroup, normal or not, has relative threshold equal to p_c on every Cayley graph
distinct_from:
  fpbs-amenable-quotient-normal-relative-threshold-is-pc: that proves the equality only for subgroups whose normal core is infinite with amenable quotient, using Gamma-invariant random Folner cells on the quotient group, and explicitly leaves non-normal co-amenable subgroups and subgroups with finite core open; this proves it for every co-amenable subgroup, including core-free ones in simple groups, with deterministic Folner sets of the Schreier graph and a mass transport over the free action of the subgroup alone.
  fpbs-tree-subgroup-relative-gap-iff-not-co-amenable: that proves on the free-group tree that co-amenable subgroups have no relative gap, using explicit tree two-point functions; this proves the no-gap half on every Cayley graph of every finitely generated group.
  fpbs-percolation-schreier-kesten-gap: that conjectures a gap for every non-co-amenable subgroup; this proves that no co-amenable subgroup has a gap, so that conjecture, if true, is an iff and cannot be extended.
  fpbs-relative-threshold-commensurability-invariant: that kills relative routes along finite-index subgroups; finite-index subgroups are co-amenable, so this is a strict generalization of that kill.
  fpbs-all-infinite-subgroups-co-amenable-class-nonuniqueness: that is the OPEN goal on the class where every infinite subgroup is co-amenable; this proves that on that class every relative-threshold route is dead on every Cayley graph.
---

**ESTABLISHED.**

**Setting.** `Gamma` is finitely generated, `S` is a finite symmetric
generating set, `G = Cay(Gamma,S)` has edges `{x, xs}`, and `I <= Gamma` is an
infinite subgroup. `p_c(I;G)` is the Hutchcroft--Pan relative threshold, the
infimum of `p` at which a.s. some open cluster meets `I` in infinitely many
vertices, as in `fpbs-relative-gap-along-any-subgroup-separates`. `I` is
**co-amenable** if there is a `Gamma`-invariant mean on `ℓ^∞(I\Gamma)`, as in
`fpbs-non-co-amenable-subgroups-have-schreier-spectral-gap`.

**Theorem.** If `I` is co-amenable, then

```text
p_c(I;G) = p_c(G),   and   chi^I_p = E_p|K_o ∩ I| = infinity for every p > p_c(G).
```

**Corollaries.**

1. **The Schreier--Kesten gap is an iff wherever it holds.** For every infinite
   `I` and every `S`: if `p_c(G) < p_c(I;G)`, then `I` is not co-amenable.
   So `fpbs-percolation-schreier-kesten-gap` is the statement
   "`p_c(G) < p_c(I;G)` iff `I` is not co-amenable", and no relative-threshold
   argument of any kind can use a co-amenable subgroup.
2. **Relative routes are dead on the whole hard core.** Let `Gamma` be
   nonamenable with every infinite subgroup co-amenable
   (`fpbs-all-infinite-subgroups-co-amenable-class-nonuniqueness`). Then on
   every Cayley graph, every infinite subgroup `I` has `p_c(I;G) = p_c(G)` and
   `chi^I_p = infinity` for all `p > p_c(G)`. So condition 1 and condition 2
   of the separation criterion fail for every subgroup. This was previously
   known only on the free-group tree and only for subgroups of finite index or
   with an infinite amenable-quotient core.
3. **Simple groups.** In a simple group every proper nontrivial subgroup has
   trivial core, so the earlier kill
   (`fpbs-amenable-quotient-normal-relative-threshold-is-pc`, Corollary 3) says
   nothing about proper subgroups. Here a relative route along a proper
   subgroup `I` of a simple group still dies whenever `I` is co-amenable. This
   covers, for example, co-amenable proper subgroups of simple
   nonamenable groups, whether of finite or infinite index.
4. **Normally co-amenable class.** On
   `fpbs-normally-coamenable-class-nonuniqueness`, a relative route must use a
   subgroup that is not co-amenable. Having finite normal core is no longer
   enough.

5. **Quantitative form, for every subgroup.** Let `h_I` be the infimum of
   `|∂F|/|F|` over finite nonempty `F ⊆ I\Gamma` in `Sch(I\Gamma,S)`, with
   `∂F` counted in arcs. Let `delta(p)` be the probability that the identity
   is a trifurcation. If `p_c(G) < p < p_u(G)` and `delta(p) > h_I`, then
   `p_c(I;G) <= p`. So a relative gap along a non-co-amenable `I` forces
   `delta(p) <= h_I` on the whole window `(p_c(G), p_c(I;G))`. Steps 3 to 5 of
   the proof give this directly, with Lemma 0 replaced by the definition of
   `h_I`.

**What is not claimed.** Nothing is claimed about non-co-amenable subgroups;
the gap there is the OPEN conjecture `fpbs-percolation-schreier-kesten-gap`.
Nothing is claimed about `p_c < p_u` itself.

Proof: `fpbs-co-amenable-subgroup-relative-threshold-is-pc-proof`.
