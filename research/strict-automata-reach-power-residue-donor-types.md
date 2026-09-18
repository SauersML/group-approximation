---
rg: 2
id: strict-automata-reach-power-residue-donor-types
kind: claim
title: If some group carries a strict automaton, some group carries a strict donor-covering automaton whose type (z, b) has z + bt a power of two for some t
distinct_from:
  strict-automata-reduce-to-two-rest-donor-covering-ones: that asks for type (2, b) with 4 ∤ b, which gives binary witnesses; this accepts every power-residue type, such as (3, 5), (5, 3) or (z, 1), and gives only binary-power witnesses, so that claim implies this one.
  some-nonsurjunctive-group-gives-a-binary-power-one: that is the bridge in terms of alphabet sizes; this is the same bridge at the level of donor-covering types, equivalent to it by item 4 of donor-covering-types-give-nonsurjunctive-size-progressions, where only the odd part of gcd(z, b) has to disappear.
  donor-covering-few-rest-automata-reach-admissible-types: that is a 2-adic type reduction on one group toward binary descent; this is a reduction from type (k, k) to any power-residue type on any group.
---

**OPEN.** Notation as in `donor-covering-types-give-nonsurjunctive-size-progressions`. If `NS_all ≠ ∅`, then some
group carries a strict donor-covering automaton of a power-residue type `(z, b)`: with `b = 2^v b'`, `b'` odd,
`2^v | z` and `z / 2^v ≡ 2^i (mod b')` for some `i >= 0`.

**Place in the graph.**
- With `donor-covering-types-give-nonsurjunctive-size-progressions` it gives
  `some-nonsurjunctive-group-gives-a-binary-power-one` (`binary-power-witness-from-power-residue-donor-types`), and it
  is implied by that claim (item 4 there). So the conjecture is exactly this claim together with
  `every-group-is-surjunctive-over-binary-power-alphabets`.
- It is implied by `strict-automata-reduce-to-two-rest-donor-covering-ones`, since types `(2, b)` with `4 ∤ b` are
  power-residue.
- **Stronger variant, one particle.** Some group carries a strict donor-covering automaton with exactly one active
  symbol. By item 2 of the established claim this puts every size above the rest count into `NS_all`.

**The step every known move misses.** A strict automaton over `k` symbols gives type `(k, k)`. Tag multiplication
gives `(z, bt)` and identity layers give `(z|P|, b|P|)`. Both keep `k | gcd(z, b)`, while a power-residue type has
`gcd(z, b)` a power of two. So from an odd `k` the claim needs a move that merges active symbols, or changes the
rest count other than by a common factor, while keeping (D2).

## Attempts

- **Reading off the type from `β × id`** (swarm-0917-w4-gs-binary-power, 2026-09-17). The only donor structures
  obtained from a bare strict `β` put the rest/active split on an identity layer, so they have types `(k m, k m')`.
  They die at the invariant `k | gcd(z, b)` above. Reclassifying rest symbols as active dies at (D2), as recorded
  under `strict-automata-reduce-to-two-rest-donor-covering-ones`.
- **Merging two layers with "active in either layer"** (same agent, 2026-09-17). On `τ × id_{r,a}` declare a site
  active if the `τ`-layer or the bit is active, with the bit layer donating to itself. (D1) holds for either
  priority rule. (D2) fails for both. With priority to the bit, an input active only in the `τ`-layer may be the
  donor only of output sites whose bit is active, and those donate to themselves. With priority to `τ`, an input
  with active bit sits at a site whose `τ`-output may be active, and then its own relay is spent on the `τ`-donor.
  So "active in either layer" is not a donor-covering split in general.
- **Letter-level moves on the transition digraph** (swarm-0917-w11-w11-gs-last1, 2026-09-17). By item 5 of
  `transition-digraph-capacity-lifts-give-nonsurjunctive-sizes`, this claim is equivalent to: some strict automaton
  has `g(τ)` a power of two. The whole letter-level class of moves is dead, by
  `block-permutation-transitions-force-divisible-classes` (established).
  - The moves in the class: products with arbitrary injective automata, letter permutations on both sides, far
    translations, capacity lifts, overgroup induction.
  - Invariant. A `k`-block permutation inside `R(τ)`. It forces `k` to divide every class, since it is the line
    digraph of a `k`-regular multigraph. Every strict automaton on `k` letters has a far translate with complete
    `R`, hence block size `k`. The moves multiply or keep block sizes.
  - Result. From strict automata with non-binary-power sizes, every strict product of the class has `g` with an odd
    factor.
  - Untranslated products. The constant permutation balances periodic classes, so
    `v_ℓ g(τ × σ) >= max(v_ℓ g(τ), v_ℓ g(σ))` as well.
  - What survives: cancellation moves that shrink `R`. These are near compositions with bijective automata (a near
    translation undoes a far one, so `g` is not a recoding invariant), powers, finite-index restriction, strict
    upset restriction, and non-product rules.
