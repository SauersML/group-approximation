---
rg: 2
id: absorptions-give-post-surjective-strict-pairs
kind: claim
title: A topological Bernoulli absorption gives a strict pair whose decoder is post-surjective, so an absorbing group is not dual surjunctive
distinct_from:
  monomial-quantum-automata-are-topological-bernoulli-absorptions: that proves absorptions are the same as strict monomial quantum automata and extracts a strict pair with a measure-preserving decoder; this proves the extracted decoder is also post-surjective and not pre-injective, which links absorptions to the dual conjecture, and adds the fixed-point, co-induction and alphabet-multiple properties of absorptions.
  post-surjective-decoders-convert-strict-pairs-to-dual-failures: that proves post-surjectivity of affine decoders and of every decoder near the encoder image; this proves post-surjectivity everywhere for the nonlinear decoders coming from absorptions, with no algebraic structure on the alphabet.
  strict-pairs-admit-post-surjective-decoders: that asks every strict pair to be replaceable by one with a post-surjective decoder; this proves it for the strict pairs that come from absorptions, so the open claim reduces to strict-automata-yield-topological-bernoulli-absorptions.
  stable-finiteness-failure-is-algebraic-bernoulli-absorption: that is the linear algebraic absorption from a Kaplansky failure; this is about arbitrary nonlinear topological absorptions, and recovers the linear post-surjectivity of Capobianco-Kari-Taati as a special case.
---

**ESTABLISHED (elementary; no novelty claimed for the individual steps)** by
[[absorptions-give-post-surjective-strict-pairs-proof]].

**Setting.** As in `monomial-quantum-automata-are-topological-bernoulli-absorptions`: `G` is a group, `A` a
finite alphabet with `|A| >= 2`, and a *topological Bernoulli absorption* is a subshift `Y` over a finite
alphabet `B` with `|Y| >= 2`, together with a shift-equivariant homeomorphism `Psi : A^G -> A^G x Y`. Say `G`
*absorbs at size `|A|`*. Post-surjective and pre-injective are as in
`post-surjective-decoders-convert-strict-pairs-to-dual-failures`.

**Theorem.** Let `Psi : A^G -> A^G x Y` be an absorption, `sigma = pr_1 o Psi`, and `y_0` the shift-fixed point of
`Y` given by (a) of the monomial theorem, with `tau(x) = Psi^-1(x, y_0)`.

1. **(i) Post-surjective decoder.** `sigma` is a post-surjective cellular automaton on `A^G` that is not
   injective and not pre-injective.
2. **(ii) Strict pair.** `(tau, sigma)` is a strict pair whose decoder is post-surjective. Hence `G` is not
   dual surjunctive at alphabet `A`: `sigma` is post-surjective and not pre-injective.
3. **(iii) Fixed-point rigidity.** For every normal subgroup `N` of `G`, `Psi` restricts to a
   `G/N`-equivariant homeomorphism `A^{G/N} -> A^{G/N} x Fix_N(Y)`. If `G/N` is surjunctive, then
   `Fix_N(Y) = {y_0}`. In particular `Fix_G(Y) = {y_0}`, and `Fix_N(Y) = {y_0}` whenever `G/N` is sofic.
4. **(iv) Co-induction and restriction.** If a subgroup `H <= G` absorbs at size `|A|`, then `G` absorbs at
   size `|A|`. Conversely, if `G` absorbs at size `|A|`, then so does the finitely generated subgroup generated
   by the memory sets of `Psi` and `Psi^-1`.
5. **(v) Multiples.** If `G` absorbs at size `d`, it absorbs at size `dm` for every `m >= 1`.

**Consequences.**
- Every absorbing group is non-amenable, and indeed nonsofic: by (ii) and Capobianco-Kari-Taati Theorem 2
  (`capobianco-kari-taati-dual-surjunctivity-toolkit`). This agrees with (a) of the monomial theorem and
  Gromov-Weiss.
- `every-group-is-dual-surjunctive` implies `no-group-carries-a-topological-bernoulli-absorption`. With the
  monomial theorem, so do `quantum-surjunctivity-conjecture` and `gottschalk-surjunctivity-conjecture`.
- `strict-automata-yield-topological-bernoulli-absorptions` implies both open transfer holes
  `strict-pairs-admit-post-surjective-decoders` and `strict-automata-yield-strict-quantum-endomorphisms`.
- By (iv), a group absorbs iff some finitely generated subgroup absorbs. So
  `no-group-carries-a-topological-bernoulli-absorption` needs checking only on finitely generated groups, and a
  single absorbing group makes every group containing it absorb.
