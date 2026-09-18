---
rg: 2
id: strict-automata-yield-topological-bernoulli-absorptions
kind: claim
title: A group carrying an injective non-surjective cellular automaton carries a topological Bernoulli absorption at some alphabet size
distinct_from:
  strict-automata-yield-strict-quantum-endomorphisms: that asks a strict pair to yield some strict quantum automaton; this asks for the stronger, purely topological datum A^G = A^G x Y, which by the monomial theorem yields a strict monomial quantum automaton and by absorptions-give-post-surjective-strict-pairs also a post-surjective decoder, so it closes that hole and strict-pairs-admit-post-surjective-decoders at once.
  strict-pairs-admit-post-surjective-decoders: that asks only for a post-surjective decoder; this asks for a decoder whose fibres are trivialized equivariantly, which implies post-surjectivity and measure preservation together.
  monomial-quantum-automata-are-topological-bernoulli-absorptions: that proves absorptions are strict monomial quantum automata and records the absorption question as an open edge; this promotes that edge to a claim, as the single hub hole of gottschalk-via-no-topological-absorption, with the necessary conditions and the dead extension recorded.
  stable-finiteness-failure-is-algebraic-bernoulli-absorption: that proves the linear case, where the strict pair comes from a one-sided inverse over F_p[G]; this asks for nonlinear strict pairs.
---

**OPEN.** Let `G` be a group. Suppose some finite full shift over `G` carries an injective, non-surjective
cellular automaton. Then for some finite alphabet `A` there is a subshift `Y` with `|Y| >= 2` and a
shift-equivariant homeomorphism `A^G -> A^G x Y`.

**Place in the graph.**
- `quantum-transfer-via-topological-absorption`: this claim implies
  `strict-automata-yield-strict-quantum-endomorphisms`.
- `post-surjective-decoders-via-topological-absorption`: this claim implies
  `strict-pairs-admit-post-surjective-decoders`, and so `dual-surjunctive-groups-are-surjunctive`.
- `gottschalk-via-no-topological-absorption`: this claim and
  `no-group-carries-a-topological-bernoulli-absorption` together give the goal. Conversely the goal implies both,
  the first vacuously. So the goal is equivalent to the conjunction.

**Necessary conditions on a decoder that works.** If `Psi = (sigma, zeta)` is an absorption and `tau = Psi^-1(., y_0)`,
then the decoder `sigma`:
- preserves the uniform Bernoulli measure ((b) of the monomial theorem);
- is post-surjective and not pre-injective (`absorptions-give-post-surjective-strict-pairs`);
- has a translation lift ((3) of the monomial theorem);
- has fibres `sigma^-1(x) = Psi^-1({x} x Y)`, all homeomorphic to one fixed subshift, with exactly one fibre
  point fixed by `N` whenever `x` is `N`-fixed and `G/N` is surjunctive
  (`absorptions-give-post-surjective-strict-pairs` (iii)).

## Attempts

- **2026-09-17 (swarm-0917-w6-w6-gs-last1, operator-algebras).** Proved `absorptions-give-post-surjective-strict-pairs`
  and set up this hub. What holds and what dies:
  - **Linear sector holds.** If the strict pair comes from a one-sided inverse `BA = I != AB` in `M_n(F_p[G])`,
    the algebraic absorption `(F_p^n)^G -> (F_p^n)^G x X_P` of
    `stable-finiteness-failure-is-algebraic-bernoulli-absorption` is a topological absorption.
  - **Subgroups.** If a subgroup of `G` carries a strict pair that absorbs, then `G` absorbs by co-induction
    ((iv) of the lemma). But non-surjunctivity of `G` does not come from a subgroup in general, so this gives
    no reduction.
  - **Dead: pointwise-additive lift.** Over `A = Z/d`, try the lift `T_e(u) = u - tau(sigma u) + tau(sigma u + delta_e)`
    of the translation `x -> x + delta_e` through the decoder. Then
    `sigma(T_e u) = sigma(r + tau z)` with `r = u - tau sigma u` and `z = sigma u + delta_e`. This equals `z` for
    all `u` exactly when `sigma(r + tau z) = z` for every residue `r` in `R = {u - tau sigma u}` and every `z`. This
    holds for affine decoders, and those already force a Kaplansky failure by
    `disjoint-footprint-decoders-force-kaplansky-failure`, where the linear sector applies. For a genuinely
    nonlinear decoder the residue shifts the decoded value, and `T_e` does not lift the translation. So this
    lift reaches nothing beyond the Kaplansky sector.
  - **No gain from track doubling.** Adding a second track `A'` that the decoder ignores and lifting translations
    only there does not lift the translations of the decoder output. Making the lift act on the first track
    brings back the fibre problem at alphabet `A`.
  - **Where it dies.** The fibre `{r : sigma(tau x + r) = x}` of a nonlinear decoder depends on `x`. An absorption
    needs an equivariant, continuous trivialization of the fibre bundle `sigma : A^G -> A^G` with a fixed
    subshift as fibre. No local construction from `(tau, sigma)` alone is known to do this.
  - **Falsifiable test.** A non-surjunctive group on which no strict pair, over any alphabet, has a measure-preserving post-surjective decoder would refute this claim.
