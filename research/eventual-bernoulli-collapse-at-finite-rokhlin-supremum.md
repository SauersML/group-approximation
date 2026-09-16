---
rg: 2
id: eventual-bernoulli-collapse-at-finite-rokhlin-supremum
kind: claim
title: Over a group with finite Rokhlin supremum, all Bernoulli shifts of sufficiently large finite base entropy are isomorphic
distinct_from:
  bernoulli-shifts-above-rokhlin-supremum-are-isomorphic: that demands collapse at every level above the supremum; this demands it only above some unspecified finite level M, and is the first of the two halves into which that claim splits.
  bernoulli-rigidity-threshold-equals-rokhlin-supremum: that asks for a nontrivial isomorphism at every level above the supremum, possibly with countable classes; this asks for one class containing all large levels and says nothing near the supremum.
  zero-rokhlin-supremum-forces-bernoulli-collapse: that asks for one isomorphism of different base entropies at supremum zero; this asks for total collapse of all large levels at every finite supremum.
  bernoulli-infinite-power-iff-approximate-half-absorption: that concerns collapse onto the infinite-entropy shift, which forces supremum zero; this concerns finite base entropies only.
  bernoulli-collapse-is-null-or-eventually-total: that proves this collapse is equivalent to D(G) = R and to non-null own-square sets, without asserting it; this asserts it.
---

**OPEN.** Let `G` be countably infinite with `s = h^Rok_sup(G) < ∞`. Then there is `M < ∞` such that all Bernoulli
shifts over `G` with base entropy in `[M, ∞)` are isomorphic.

**Equivalent forms** (`bernoulli-collapse-is-null-or-eventually-total`, item 2):
- `D(G) = R`;
- `D(G)` is not Lebesgue-null;
- some isomorphism class of base entropies is not null;
- the own-square levels `{h : X_h ≅ X_h × X_h}` form a non-null set, or a non-meager one.

**Consequences.**
- Together with `bernoulli-rigidity-threshold-equals-rokhlin-supremum`, it gives
  `bernoulli-shifts-above-rokhlin-supremum-are-isomorphic`, through route
  `above-supremum-collapse-from-eventual-collapse-and-descent`.
- At `s = 0` it gives `D(G) ≠ {0}`, which is the conclusion of `zero-rokhlin-supremum-forces-bernoulli-collapse`.
- If some group has `0 < s < ∞`, it would give `D(G) ≠ {0}` with `s > 0` for that group. That would answer
  negatively the question, recorded on `bernoulli-isomorphism-collapse-set-is-a-subgroup`, whether collapse forces
  `s = 0`.

**Model tests.**
- Sofic groups have `s = ∞`, so the claim is vacuous there.
- No group with `s < ∞` is known.
- The formal relation "`a ≈ b` iff `a = b` or `a, b > s` with `b − a` in a countable dense subgroup" satisfies
  translation, transitivity, analyticity and Seward's threshold (the formal content of items 1–4 and 6 of
  `bernoulli-isomorphism-collapse-set-is-a-subgroup`), and fails this claim. So no argument using only that calculus can prove it (artifact of
  `bernoulli-collapse-is-null-or-eventually-total`, Section 5).

## Attempts

- **Countably many explicit isomorphisms (dies at a null relation).**
  - Composing, inverting and multiplying by Bernoulli factors a countable list of seed isomorphisms relates each
    level `a` only to `a + Γ`, where `Γ` is a countable group (item 5 of
    `bernoulli-collapse-is-null-or-eventually-total`).
  - Finitary codes, a single `2^G ≅ 3^G`, or countably many own-squares therefore never reach the non-null set
    this claim needs. A proof must produce uncountably many isomorphisms not related by the calculus, or use a
    closure principle.
- **Closure principle (dies at finite determination).**
  - If the relation `X_a ≅ X_b` were closed in the plane, two rationally independent elements of `D(G)` would
    suffice (artifact Section 6).
  - The natural source of closure is finite determination of Bernoulli measures. On Thompson's `V` at supremum
    zero it fails (`thompson-v-bernoulli-finitely-determined-iff-pos`).
- **Baire category on i.i.d. partitions (dies at the spectral gap).**
  - Density of generating i.i.d. partitions would give total collapse
    (`zero-supremum-collapse-via-dense-iid-generators`).
  - That density fails on every group with zero supremum (`spectral-gap-refutes-exactification-on-nonamenable-groups`).
  - Every Bernoulli class is meager in the space of actions on product hosts with a central locally finite factor
    (`bernoulli-classes-meager-on-central-locally-finite-hosts`).
- **Self-similarity from one own-square (dies at the transfer to `G`).**
  - `X_h ≅ X_h × X_h`, iterated, lets coordinate permutations of `X_h^(2^n)` act on `X_h` commuting with `G`.
    This gives an action of `G × P`, with `P` an increasing union of iterated wreath products of `Z/2`
    (freeness not checked).
  - `h^Rok_sup(G × P) = 0` already follows from Seward's Theorem 1.11 (arXiv:1501.03367v4: if `P` contains
    arbitrarily large finite subgroups and `h^Rok_sup(G) < ∞`, then `h^Rok_sup(P × G) = 0`; statement read from
    the PDF on 2026-09-16). Nothing transfers back to the `G`-isomorphism classes, and the construction yields
    only countably many isomorphisms.
- **Invariants (no obstruction either way).** Rokhlin entropy `min(h, s)`, relative Rokhlin entropy `min(b, s)`
  of a split Bernoulli factor (Proposition 6.5 of arXiv:1501.03367) and every semicontinuous invariant are
  constant above `s` (`semicontinuous-invariants-blind-above-rokhlin-supremum`). So none of them can refute this
  claim.
