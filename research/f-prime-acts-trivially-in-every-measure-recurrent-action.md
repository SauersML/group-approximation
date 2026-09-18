---
rg: 2
id: f-prime-acts-trivially-in-every-measure-recurrent-action
kind: claim
title: "If some probability measure whose support generates a countable group G as a semigroup induces a recurrent chain on a transitive G-set, every homomorphic image of F′ in G fixes that set pointwise; no moment, support, symmetry or finite-generation condition is needed"
distinct_from:
  f-functor-cocycles-need-an-exotic-recurrent-action: its item 2 uses the JMBMdlS notion of a recurrent action (recurrent for every symmetric finitely supported measure) and takes the uniform measure on a generating set of F itself; this assumes recurrence for one arbitrary measure on G, which may be infinitely supported, heavy-tailed and non-symmetric, on a group that need not be finitely generated.
  thompson-f-recurrent-f-sets-factor-through-the-abelianization: that is the statement for Schreier graphs of F with a finite generating set; this transfers it to every chain induced by any generating measure on any countable group containing an image of F, through subordination, symmetrization and a capacity comparison.
  thompson-f-does-not-embed-in-wobbling-groups-of-recurrent-graphs: that transfers the same base theorem to bounded-displacement actions on recurrent bounded-degree graphs by rough embeddings; this needs no graph, no bounded displacement and no degree bound, only recurrence of one induced chain.
  recurrent-orbits-force-every-z3-to-meet-the-stabilizer: that works with finite symmetric generating multisets of a finitely generated group; this removes finite support and symmetry for the conclusion about F′.
  thompson-f-dyadic-orbit-walks-are-transient: that imports Kaimanovich's transience for the one action F on the dyadic rationals; this covers every action of every countable group with F′ acting nontrivially, and recovers that citation as the special case G = F, X = D.
  f-dyadic-action-is-not-recurrent: that proves ballistic mean inverted orbit for finitely supported symmetric measures on F acting on the dyadic rationals; this gives ballistic mean inverted orbit for every generating measure in every host where F′ acts nontrivially.
---

**ESTABLISHED** by `f-prime-trivial-in-measure-recurrent-actions-proof` (not yet refereed).

**Setting.**
- `G` is a countable group, `θ : F → G` a homomorphism (not necessarily injective), and `X` a
  transitive `G`-set.
- `μ` is a probability measure on `G` whose support generates `G` as a semigroup. It may be
  infinitely supported, have no moments, and be non-symmetric. `G` need not be finitely generated.
- The *induced chain* is `P(y,z) = μ{g : g y = z}` on `X`. It is irreducible, and doubly stochastic
  because each `g` is a bijection.

**Theorem.** If the induced chain is recurrent, then `θ(F′)` fixes every point of `X`.

**Corollaries.**
1. **Ballistic inverted orbits in every faithful-type host.** Suppose `θ(F′)` moves some point of the
   transitive `G`-set `X`. Then for every `μ` as above, the induced chain is transient, and the inverted
   orbit `O_n = {h_1 ⋯ h_k x : 0 ≤ k ≤ n}` (with `h_i` i.i.d. of law `μ`) satisfies
   `(1/n) E|O_n| → P_x(T⁺ = ∞) > 0`.
   - So the sufficient condition "`(1/n) E|O_n| → 0` for some measure" for extensive amenability fails in
     every such host, for every measure. Any extensive-amenability certificate for such an action must use
     the rare-event confinement of `f-dyadic-ea-iff-inverted-orbit-confinement`, not a mean bound.
   - With `G = F`, `X = D` this recovers the transience in `thompson-f-dyadic-orbit-walks-are-transient`
     for every strictly non-degenerate measure.
2. **Full-group hosts.** Let `G` be any countable group of permutations of a set `Y`, for instance a countable
   subgroup of a topological full group `[[H ↷ Y]]`, and suppose `G` contains a copy of `F` whose commutator
   subgroup moves a point of the `G`-orbit `G·y`. Then no measure on `G` whose support generates `G` as a
   semigroup induces a recurrent chain on `G·y`. So a recurrence-based proof of extensive amenability of the host
   (Juschenko–Nekrashevych–de la Salle and its descendants) cannot be run on any orbit where the copy of `F′`
   acts, whatever measure is chosen.

**Scope.** The Theorem does not touch extensive amenability of transient actions, which is where
`thompson-f-dyadic-action-is-extensively-amenable` lives. It closes the loophole in which a heavy-tailed,
infinitely supported or non-symmetric measure on a larger, possibly infinitely generated host would be recurrent
while every finitely supported symmetric measure on `F` is transient: such a measure only adds conductance
(after symmetrization), so it cannot be more recurrent.

Proof route: `f-prime-trivial-in-measure-recurrent-actions-proof`.
