---
rg: 2
id: every-group-is-surjunctive-over-binary-power-alphabets
kind: claim
title: Every group is surjunctive over every alphabet whose size is a power of two
distinct_from:
  every-group-is-binary-surjunctive: that is the two-symbol alphabet only; this is every size 2^n, which implies it by product closure, while the converse would need descent from 2^n to 2.
  gottschalk-surjunctivity-conjecture: that is every finite alphabet; this is the binary-power alphabets, which give the conjecture exactly when strictness ascends to larger alphabets.
  stable-finiteness-forces-binary-surjunctivity: that is the conditional statement for one group from stable finiteness of F_2[G]; this is the unconditional universal statement over binary-power alphabets.
artifacts:
  - research/artifacts/formalizability-prime-fields-and-alphabet-bridge-2026-09-12.md
---

**OPEN.** For every group `G` and every `n >= 1`, every injective cellular automaton on `A^G` with
`|A| = 2^n` is surjective.

**Place in the graph.**
- It is implied by the conjecture.
- It implies `every-group-is-binary-surjunctive` (`strict-rule-pairs-pass-to-product-alphabets`).
- It gives the conjecture through `gottschalk-via-alphabet-ascent`, if strictness ascends to larger
  alphabets.

## Attempts

- **Through Kaplansky.** It would follow from stable finiteness of `F_2[G]` for every group together with
  `stable-finiteness-forces-binary-surjunctivity`, whose route needs a formalizability claim
  (`binary-left-inverse-pairs-are-formalizable`, or `prime-field-left-inverse-pairs-are-stably-formalizable`).
  All three are open.
- **Linear binary case.** Linear rules over `F_2^n` are matrix Kaplansky pairs over `F_2[G]`. They are
  excluded exactly where `F_2[G]` is stably finite.
- **Where it stops.** Kaplansky stable finiteness over `F_2` is open for nonsofic groups, and every
  candidate counterexample host in the graph is nonsofic.
- **Power-residue donor types** (swarm-0917-w4-gs-binary-power, 2026-09-17). A direct proof is out of reach, since
  it implies Kaplansky stable finiteness over `F_2` for all groups. So the work went to the partner bridge of
  `gottschalk-via-binary-power-nonsurjunctive-witness`.
  - `donor-covering-types-give-nonsurjunctive-size-progressions` (established) shows that a strict donor-covering
    automaton of type `(z, b)` puts `z + bt` in `NS(G)` for every `t >= 1`.
  - By item 5 there, this claim forbids every strict donor-covering automaton of power-residue type (some
    `z + bt = 2^j`). That includes one active symbol over any number of rest symbols. So a counterexample may be
    sought as a strict automaton with a single moving, relayed particle, over any alphabet size.
  - The bridge is equivalent to `strict-automata-reach-power-residue-donor-types` (open). Together with that claim,
    this one gives the conjecture (`binary-power-witness-from-power-residue-donor-types`).
  - `single-active-symbol-strict-donor-automata-give-every-size` (established, from the collapse-lift theorem) shows
    that a one-particle witness would give `2 ∈ NS(G)`. So that recipe targets binary surjunctivity itself.
  - Where it stops: every known move keeps the odd part of `gcd(z, b)`.
- **Transition-digraph capacity lifts** (swarm-0917-w5-gs-binary-power, 2026-09-17). This picks up from the donor
  reduction and drops the donor map and the residue arithmetic.
  - `transition-digraph-capacity-lifts-give-nonsurjunctive-sizes` (established, elementary) shows that a strict `τ`
    puts every sum `Σ n(a)` in `NS(G)` when `n >= 1` is monotone along the letter-transition digraph
    `R(τ) = {(x(g), τ(x)(g))}`. The lift writes `(τ(x)(g), i_g)`. So `NS(G)` holds all large multiples of `g(τ)`,
    the gcd of the class sizes of `R(τ)`.
  - This claim is equivalent to: no strict automaton over any group has `g(τ)` a power of two. In particular every
    injective automaton with a letter `c` whose transition class is `{c}` is surjective. Such a letter may persist
    or dissolve but is never re-created from other letters, and a strict one would make `NS(G)` cofinite. The
    bridge `some-nonsurjunctive-group-gives-a-binary-power-one` is equivalent to reaching a strict `τ` with
    `g(τ)` a power of two.
  - A strict automaton has no sitewise indestructible letter, i.e. no upset of size one (charge noncreation).
  - The sitewise-label letter-collapse lifts reach exactly the capacity sums. So the rule-specific covers of the
    bridge Attempts that can change the odd part must mix labels across sites. There, when the largest fiber is
    unique, `collapse-lifts-with-unique-largest-fiber-are-surjective` applies.
  - Where it stops: identity layers and capacity lifts keep `g`. Powers `τ^p` refine classes, since
    `R(τ^p) ⊆ R(τ)^p`, and bijective conjugations change `R`. No move is known that splits a class of odd size.
