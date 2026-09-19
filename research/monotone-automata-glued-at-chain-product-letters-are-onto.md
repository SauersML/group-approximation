---
rg: 2
id: monotone-automata-glued-at-chain-product-letters-are-onto
kind: claim
title: Over every group, a monotone injective automaton is surjective when some letter has meets and joins with every letter and a product-of-chains ideal and filter
distinct_from:
  monotone-chain-product-automata-are-layer-translations: that is the case where the whole alphabet is a product of chains, with a rigid layer structure; this glues two such pieces at one letter and proves surjectivity by a weighted charge, without a rigid normal form.
  monotone-injective-chain-automata-are-translations: that splits a chain at an interior level, where the two sides are chains and one defect count works; this splits at a letter whose sides are products, where a defect incomparable with the letter must be charged on both sides.
  finite-injective-charge-noncreation-forces-surjectivity: that is the tool used; this is a class of monotone automata on which its nonincrease hypothesis is verified.
artifacts:
  - experiments/monotone-lattice-glue-2026-09-17/lattice_monotone_search.py
  - experiments/monotone-lattice-glue-2026-09-17/lattice_search_results.txt
---

**ESTABLISHED** by `monotone-automata-glued-at-chain-product-letters-are-onto-proof`, from
`monotone-chain-product-automata-are-layer-translations` and `finite-injective-charge-noncreation-forces-surjectivity`.

**Theorem.** Let `G` be any group and `L` a finite poset. Suppose some letter `c ∈ L` satisfies:
- (a) for every `d ∈ L`, the meet `d ∧ c` and the join `d ∨ c` exist in `L`. This holds in every lattice, and for
  every `c` comparable with all letters;
- (b) the ideal `↓c = {d : d <= c}` and the filter `↑c = {d : d >= c}` are each order-isomorphic to a product of
  finite chains (a one-letter poset counts as the empty product).

Then every injective cellular automaton on `L^G` that is monotone (`x <= x'` implies `ρ(x) <= ρ(x')`) is surjective.
Moreover, after a power fixing constants, `ρ` conserves the charge
`W(x) = Σ_g (w_-(x(g) ∧ c) + w_+(x(g) ∨ c))` on configurations that differ from `c^G` at finitely many sites. Here
`w_-(d)` counts the factors of `↓c` in which `d` is below the top, and `w_+(d)` counts the factors of `↑c` in which
`d` is above the bottom.

**Alphabets covered.** In each case below, no strict monotone automaton exists over any group.
- Every product of chains (take `c` the bottom).
- Every lattice of length two, `M_n = {0 < a_1, ..., a_n < 1}`, with `c = a_1`. In `M_3` the letters `a_2, a_3` are
  incomparable with `c`, which is where the two-sided charge is needed.
- The pentagon `N_5`, with `c` the atom on the long side. Both sides are then chains.
- Every lattice with an atom `a` such that `[a, 1]` is a product of chains, and dually with a coatom.
- Every ordinal sum `P ⊕ {c} ⊕ Q` in which `P ⊕ {c}` and `{c} ⊕ Q` are products of chains, for example
  `1 ⊕ (2 x 2)`, the lattice of down-sets of the V-shaped poset.

**What this kills.** In `monotone-strict-automata-ascend-along-poset-homs`, a strict monotone automaton on `L` would
make every `|Hom(P, L)|` a nonsurjunctive size. This theorem removes every alphabet above from that mechanism. The
invariant is the two-sided charge `W`. The class dies at the nonincrease step. The ideal side is bounded through
`ρ(x ∧ c) <= ρ(x) ∧ c`, the filter side through `ρ(x) ∨ c <= ρ(x ∨ c)`. The layer rigidity of the two sides makes
both side charges exact, so `W` never grows.

**What survives.**
- Connected posets where no letter has both meets and joins with every letter, for example the V shape
  `{0 < a, 0 < b}`, fences and crowns. Remark 2 of the proof shows that the V shape falls to a direct local sandwich.
  That is recorded as a sketch, not as a node.
- Lattices where no letter has a product-of-chains ideal and filter, first `M_3 ⊕ M_3` (two diamonds stacked at a
  letter). The obstruction to iterating is that the theorem yields surjectivity and conservation of `W` at `c`, but
  no nonincreasing charge at the extreme backgrounds of `L`. Gluing needs exactly such a charge on each side.
- Disconnected posets. For an antichain, every automaton is monotone, so that case is the full conjecture.
