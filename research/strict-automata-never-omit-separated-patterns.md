---
rg: 2
id: strict-automata-never-omit-separated-patterns
kind: claim
title: No injective automaton omits a letter or a pattern whose cells are separated by a sofic quotient, so the separated-defect route to the binary-power bridge is empty
distinct_from:
  separated-omitted-patterns-make-nonsurjunctive-sizes-cofinite: that derives cofinite NS from a strict automaton omitting a letter or a profinitely separated pattern; this shows those hypotheses are never satisfied, so that claim holds vacuously and reduces nothing.
  injective-automata-restrict-to-schreier-graph-automata: that proves the fixed configurations of one subgroup lie in the image; this combines finitely many normal subgroups through soficity permanence, and draws the consequence for omitted patterns and for the bridge.
  sofic-radical-localizes-garden-of-eden-windows: that puts a nontrivial sofic-invisible element in Omega^-1 Omega by almost-multiplicative counting; this is the elementary periodic-point version, and it adds that the omitted pattern takes different values across that element.
  some-nonsurjunctive-group-gives-a-binary-power-one: that is the bridge; this closes one family of attacks on it.
  surjunctivity-passes-to-quotients: that asks whether surjunctivity descends to quotients; this uses only that an injective automaton over G restricts to one over a quotient.
  transition-digraph-capacity-lifts-give-nonsurjunctive-sizes: that turns upsets of the transition digraph into sizes; this shows the singleton-complement upset of an omitted letter never exists.
---

**ESTABLISHED** by `strict-automata-never-omit-separated-patterns-proof`.

Let `τ : A^G -> A^G` be an injective cellular automaton over a group `G`, and `X = τ(A^G)`. Call a finite
pattern `w ∈ A^F` **omitted** if no translate of any configuration in `X` restricts to `w` on `F`. Let `Σ(G)`
be the intersection of all normal subgroups `N` with `G/N` sofic, and `K(G)` the intersection of all
finite-index subgroups. Then `Σ(G) ⊆ K(G)`.

1. **Periodic points.** For `N ⊲ G` with `G/N` surjunctive, every configuration constant on the cosets of `N`
   lies in `X`.
2. **No omitted letter.** Every letter occurs in every image. Equivalently, `τ` permutes the constant
   configurations.
3. **No separated omitted pattern.** If `w ∈ A^F` is omitted, there are `f, f' ∈ F` with `w(f) ≠ w(f')` and
   `f^(-1) f' ∈ Σ(G) \ {1}`. In particular `F F^(-1) ∩ K(G) ≠ {1}`, and `F` is separated by no finite-index
   subgroup.
4. **Transfer.** If a strict datum `(μ, ν, w)` over `G` transfers to a group `G'` sharing its `2r`-ball, as in
   item 4 of `separated-omitted-patterns-make-nonsurjunctive-sizes-cofinite`, then item 3 holds in `G'` too.
   So `F̃ F̃^(-1)` meets `Σ(G') \ {1}` in every such `G'`, including every finitely presented cover `G_L`.

## Consequences

- **The w11 claim is vacuous.** `separated-omitted-patterns-make-nonsurjunctive-sizes-cofinite` has four
  hypotheses: an omitted letter (item 1), a pattern separated by a finite-index subgroup (item 2),
  `F F^(-1) ∩ K = {1}` (item 3), and the same condition in some `G_L` (item 4). Items 2, 3 and 4 here show that
  none of them is ever met by an injective automaton. Its item 5 is also trivial: an injective automaton
  `A^G -> B^G` sends the `|A|` constant configurations injectively to constants, so `|A| <= |B|`.
- **Its search target is impossible.** "An image that misses one symbol" does not exist over any group.
- **Class killed.** Every attack on the bridge that makes a defect of strict data visible in a surjunctive
  quotient dies at item 1. This covers letter omission, regrouping over finite-index subgroups,
  separation in finitely presented covers, and restriction to sub-alphabets checked on periodic points.
  - **Invariant.** Every omitted pattern takes two values on some coset of `Σ`.
  - **Where each member dies.** At the bijection of `τ` on `Fix(N)`, for `N ⊲ G` with `G/N` sofic.
- **What a bridge witness must do.** It must convert strict data whose every defect folds modulo the sofic
  residual. This holds in the host and in every group sharing the relevant ball.

## Attempts
