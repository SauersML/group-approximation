---
rg: 2
id: shear-designs-are-strict-iff-their-key-automaton-is
kind: claim
title: An automaton that runs a key automaton and permutes each data symbol under key control is strict exactly when the key automaton is
distinct_from:
  controlled-self-linear-feedback-ca-are-surjunctive: that peels rows linear in their own block under controllers reading later blocks, with bijective constant parts; this lets the key block run any automaton and the data row any key-controlled permutation, and transfers injectivity and surjectivity in both directions.
  bijective-designs-force-every-finite-presentation: that builds shift–shear designs forcing any presentation with a bijective encoder; this proves no key-controlled data shear can make a design strict, whatever it forces, unless the key automaton is strict already.
  triangular-forward-tables-force-surjectivity: that decides bijectivity from the table group of a forward partition; this decides strictness from the architecture of the encoder, independently of every forward table.
artifacts:
  - research/artifacts/vh-lattice-table-hosts-2026-09-12.md
  - research/artifacts/gk-vf-nonlinear-verification-2026-09-12.md
---

**ESTABLISHED** by `shear-design-key-automaton-reduction-proof`.

Let `G` be any group and `A = K x D` a product of finite alphabets. Let
`kappa : K^G -> K^G` be a cellular automaton, `N` a finite subset of `G`, and
`pi : K^N -> Sym(D)` any map. Define

    tau(x)(g) = ( kappa(x_K)(g),  pi( (x_K(g n))_(n in N) ) (x_D(g)) ).

**Theorem.** `tau` is injective iff `kappa` is, and surjective iff `kappa` is. So `tau` is
strict iff `kappa` is strict.

**Consequences.**
- The shift–shear designs are bijective because their key automaton is a product of
  translations, which recovers Lemma 4 of `bijective-designs-force-every-finite-presentation`.
- **Square-read shift–shear designs are never strict.** Suppose the key automaton acts
  track by track, and each track automaton reads at most two addresses. A track
  automaton `k -> phi(k(. v), k(. h))` is a translation followed by an automaton with
  memory `{1, v^(-1) h}`, which acts coset by coset on the cyclic group `< v^(-1) h >`. Cyclic
  groups are residually finite, hence surjunctive, so the design is injective only if
  bijective. This holds over every group, lattices in products of trees included,
  whatever squares the data shear forces and whatever its reverse hinges are.
- Coincidences forced only through a key-controlled data shear never bear on
  strictness. A strict design of this shape needs a strict key automaton, whose own left
  inverse must force a nonsofic core (`forward-relations-of-a-counterexample-have-a-nonsofic-core`).

Proof: Section 6 of the artifact.
