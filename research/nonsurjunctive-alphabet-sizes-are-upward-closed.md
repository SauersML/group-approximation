---
rg: 2
id: nonsurjunctive-alphabet-sizes-are-upward-closed
kind: claim
title: A group that is not surjunctive over k symbols is not surjunctive over any larger alphabet
distinct_from:
  strict-rule-pairs-ascend-to-larger-alphabets: that is ascent with the tables fixed, for arbitrary table pairs, and it is refuted; this is ascent for one group, where the memories and the realized tables may change.
  ec-groups-share-the-nonsurjunctive-alphabet-sizes: that proves NS(G) closed under multiples and equal to NS_all on existentially closed groups; this asks for closure under every larger size.
  surjunctivity-failure-descends-to-binary-alphabet: that moves the failing size down to two; this moves it up to every larger size.
  table-pair-strict-exactly-at-composite-alphabet-sizes: that is one table pair, realized in no group, whose admissible sizes are the composites; this is ascent for realized data, which that example cannot decide.
artifacts:
  - research/artifacts/composite-size-strict-table-2026-09-16.md
---

**OPEN.** In the notation of `ec-groups-share-the-nonsurjunctive-alphabet-sizes`: for every group `G`, if `k ∈ NS(G)` and
`n >= k`, then `n ∈ NS(G)`. The memories and the realized tables may change.

**Place in the graph.**
- It is the group-level consequence formerly recorded under `strict-rule-pairs-ascend-to-larger-alphabets`. That
  table-level claim is refuted by `table-pair-strict-exactly-at-composite-alphabet-sizes`.
- With `every-group-is-surjunctive-over-binary-power-alphabets` it gives the conjecture
  (`gottschalk-via-upward-closed-nonsurjunctive-sizes`).
- The invalidated route `linear-sofic-surjunctivity-via-formalizability-and-ascent` used only this group-level statement
  for the group at hand, so it can be rebuilt over this claim.
- It holds vacuously if the conjecture holds.

## Attempts

- **Fixed tables** (swarm, 2026-09-16). This was the refuted claim `strict-rule-pairs-ascend-to-larger-alphabets`. A
  2 x 3 table pair is strict exactly at the composite sizes (`table-pair-strict-exactly-at-composite-alphabet-sizes`).
  - What the example is not. It is not realized in any group, since `x_b = 1` forces `(1,a) ~ (b,a)` in the reverse
    table, and the two-digit code needs that coincidence to fail.
  - What it forces. A proof must use that the tables come from a group, or must change the tables, for instance by
    enlarging the memories.
  - Realized pairs cannot help. A table pair realized in a group with any strict size already refutes the
    conjecture, so realized-table ascent cannot be refuted by any example short of that.
  - Artifact `research/artifacts/composite-size-strict-table-2026-09-16.md`, Section 4.
- **Multiples only.** `ec-groups-share-the-nonsurjunctive-alphabet-sizes` gives `k l ∈ NS(G)` for every `l >= 1`, and no
  more. The smallest instance not covered is `k ∈ NS(G)` implies `k + 1 ∈ NS(G)`, for example `2` implies `3`.
- **Passive extensions are dead at group level.** `passive-fixing-injective-automata-are-surjective`: an injective
  automaton that fixes the added symbols in place and writes no added symbol at an original site is surjective. So the
  walls design recorded under `strict-rule-pairs-ascend-to-larger-alphabets` cannot be repaired. An ascent from `A` to
  `A ⊔ D` must write at `D`-sites, or write `D`-symbols at `A`-sites.
- **Existentially closed groups.** `NS(K) = NS_all` for existentially closed `K`, so the claim for one such `K` says
  exactly that `NS_all` is upward closed. That universal form already suffices for the route to the conjecture. The
  per-group form is needed for per-group applications such as linear soficity.
- **Moving one extra bit** (a-gs-upward-closed, 2026-09-17). The design: split one letter `a0` of a strict `τ` into
  `|Q|` letters, and carry the extra data along a local matching of `a0`-sites, or by any injective map that copies
  it by a translation away from the defects. It dies over every group, by
  `translating-transport-split-lifts-are-surjective`.
  - The step where it dies. The lift forces `τ(a0^G) = a0^G`. The cofinite translation makes the finite injection
    `Q^{F \ E} -> Q^{Fs \ E'}` count `|E(τ u)| <= |E(u)|`. Charge noncreation then makes `τ` and the lift surjective.
  - What survives among lifts.
    - One-letter splits whose rest bit map `T_0` on `Q^G` is a bijective automaton that is not a relabelled
      translation. If `T_0` is not surjective, then `|Q| ∈ NS(G)` already.
    - Splits of two or more letters. The charge is then degenerate, and the product lifts giving the multiples sit
      here.
    - Ascents that commute with no letter collapse.
  - By-product. `reversible-automata-that-never-lower-rest-counts-preserve-them` holds over every group, by
    `rest-count-preservation-from-charge-noncreation`. So the count-raising hypothesis of
    `count-raising-reversible-automata-lower-biased-rokhlin-entropy` is never met, and the autonomous star designs die
    unconditionally.
- **Any letter-collapse lift, any rest map** (swarm-0917-w4-gs-upward, 2026-09-17). The first survivor above is
  dead too, and so is the whole collapse class for `k -> k+1`, unless `2 ∈ NS(G)`. By
  `collapse-lifts-with-unique-largest-fiber-are-surjective`, if `Φ` is injective on `B^G`, `r ∘ Φ = τ ∘ r` for a
  letter collapse `r : B -> A` and an injective `τ`, and the largest fiber `Q0` is unique, then either
  `|Q0| ∈ NS(G)` or `τ` and `Φ` are both surjective.
  - The step where the class dies. The rest map `T_0 = Φ|_{Q0^G}` is an injective automaton. If it is not
    surjective, `|Q0|` already fails. If it is bijective, it preserves the uniform Bernoulli measure
    (`bijective-ca-preserve-uniform-bernoulli-measure`). A window count over a finite defect then gives
    `W(τ u) <= W(u)` for the charge `w(a) = log(|Q0| / |Q_a|)`, and charge noncreation makes `τ` and `Φ` surjective.
    The translation of the earlier attempt is no longer needed.
  - Invariant. The fiber charge `W(u) = Σ_g log(|Q0| / |Q_{u(g)}|)`: every collapse lift with a bijective rest map
    conserves it.
  - For `n = k + 1`. Every collapse `B -> A` has a unique fiber of size `2`. So over a group with `2 ∉ NS(G)`, an
    ascent `k -> k+1` must not commute with any letter collapse onto an injective automaton. If `2 ∈ NS(G)`, the
    step `k -> k+1` is needed only for even `k`, because odd `k` gives even `k+1` as a multiple of `2`.
  - What survives. (i) Collapses with at least two largest fibers, for example `(2,2,1)` from `3` to `5`, and the
    product lifts. (ii) Ascents with no collapse onto an injective automaton, for instance lifts over a
    non-injective `τ'`, or block-code factors instead of letter maps.
  - By-product (descent). A strict automaton on `n >= 3` symbols with one autonomously evolving letter, whose
    occurrence set moves by an injective binary automaton, gives `n - 1 ∈ NS(G)`.
- **Dual background, smallest fiber** (swarm-0917-w5-gs-upward, 2026-09-17). This kills survivor (i) above whenever the
  smallest fiber is unique, including the named example `(2,2,1)` from `3` to `5`. By
  `smallest-fiber-collapse-lifts-are-surjective` (established, route `smallest-fiber-collapse-dual-background-proof`),
  suppose `r ∘ Φ = τ ∘ r` with `τ` bijective, `Φ` injective, and a unique smallest fiber `Q0` of size `s`. Then
  `s ∈ NS(G)` (only possible if `s >= 2`), or `Φ` is surjective.
  - The step where the class dies. Replace `Φ` by a power fixing every constant. The rest map on `Q0^G` is then
    bijective, or `s` already fails. The same window count as before gives `W'(u) <= W'(τ u)` with
    `w'(a) = log(|Q_a| / s)`. That is the opposite sign, so it controls `τ^{-1}`, not `τ`. `τ^{-1}` is an automaton that
    fixes `a0^G`, preserves finiteness and never creates `W'`. Charge noncreation gives equality, and the fiber
    injections become bijections.
  - Invariant. The fiber charge relative to the smallest fiber, `W'(u) = Σ_g log(|Q_{u(g)}| / s)`.
  - Consequence for ascent. Suppose a strict collapse design sits over a bijective base, and neither extreme fiber size
    already lies in `NS(G)`. Then it needs two letters of the largest size and two of the smallest (or equal
    fibers). The first undecided profile is `(2,2,1,1)`.
  - Autonomous region. Let `j < n/2` letters have an occurrence set that moves by an injective automaton. Then a strict
    automaton on `n` letters gives `n - j ∈ NS(G)`, and `2 ∈ NS(G)` or `j ∈ NS(G)`. So over a group with
    `2 ∉ NS(G)`, ascent `k -> k + j` by an autonomously moving region of `j < k` new letters needs `j ∈ NS(G)`.
    The case `j = 1` recovers the dead star designs.
  - What survives.
    - Profiles with two letters of each extreme size.
    - A base `τ` that is strict but on fewer letters (`|A| ∈ NS(G)`, which says nothing about `n`).
    - Block-code factors.
    - Coupled dynamics with no factor onto an injective automaton.
- **Order-theoretic ascent** (swarm-0917-w14-w14-gs-break, reframing, 2026-09-17). This is a new ascent mechanism,
  and its strongest cases are killed.
  - Mechanism, from `monotone-strict-automata-ascend-along-poset-homs` (established, route
    `monotone-strict-automata-ascend-along-poset-homs-proof`). Let `ρ` be strict on `L^G` and monotone for a partial
    order on `L`. Then `f ↦ ρ ∘ f` is strict on `Hom(P,L)^G` for every finite poset `P`, so `|Hom(P,L)| ∈ NS(G)`.
    - On the two-letter chain this would give every `n >= 2`: upward closure and descent to `2` at once.
    - On a `k`-chain it gives the multichain counts, which are not multiples of `k` (`10` from `3`).
  - Kill, from `monotone-injective-chain-automata-are-translations` (established, route
    `monotone-injective-chain-automata-are-translations-proof`). Over every group, a monotone injective automaton on a
    finite chain is a copy of one coordinate.
    - Proof: induction on chain length, splitting at level `1` and using charge noncreation.
    - So no linear order on any alphabet makes a strict rule monotone. Threshold, max-min and sorting rules are all
      dead.
    - The exhaustive search over `Z` in `experiments/monotone-poset-ascent-2026-09-17/` agrees.
  - Reduction. After a power fixing constants, every chain interval of `L` is invariant and is acted on by a copy. The
    automaton descends to the connected components of the order. For connected `P`, the ascent is a letter-collapse
    lift of that component automaton, with fibers `|Hom(P, L_i)|`. So the collapse-lift obstructions above apply.
  - What survives.
    - Connected non-chain orders, first the Boolean square `2 × 2` (monotone pairs of binary layers). A strict one
      would give every square `>= 4`.
    - Disconnected orders whose component automaton is not injective.
- **Order-theoretic ascent on lattices** (swarm-0917-w18c-w18c-gs-alt, symbolic-dynamics, 2026-09-19). The Boolean
  square survivor is dead, and so are products of chains and lattices glued from them at one letter.
  - Products of chains, from `monotone-chain-product-automata-are-layer-translations` (established, route
    `monotone-chain-product-automata-are-layer-translations-proof`). Over every group, a monotone injective
    automaton on `C_1 x ... x C_m` is, after a power fixing constants, a translation on each layer, and so it is
    bijective. The translations may differ between layers.
    - The step where it dies. With the other layers on constant backgrounds, each layer slice is an invariant
      chain subshift. The chain theorem makes it a translation. The layer value is sandwiched between the all-bottom
      and all-top slices, which forces one translation per layer.
    - So the Boolean square gives no strict monotone rule. The "every square `>= 4`" ascent never fires, and neither
      does any Boolean lattice, grid or divisor lattice.
  - Gluing, from `monotone-automata-glued-at-chain-product-letters-are-onto` (established, route
    `monotone-automata-glued-at-chain-product-letters-are-onto-proof`). Suppose a letter `c` has meets and joins with
    every letter, and `↓c` and `↑c` are products of chains. Then every monotone injective automaton is surjective.
    - Invariant. The two-sided charge `w(d) = w_-(d ∧ c) + w_+(d ∨ c)`, the layer counts of the meet and join.
    - The step where it dies. `ρ(x ∧ c) <= ρ(x) ∧ c` and `ρ(x) ∨ c <= ρ(x ∨ c)`, together with the exact layer
      counts on both sides, give `W(ρx) <= W(x)`. Charge noncreation then gives surjectivity.
    - This covers `M_n` for every `n`, `N_5`, every lattice of length two, and `1 ⊕ (2 x 2)`.
  - Census over `Z`, window 2, in `experiments/monotone-lattice-glue-2026-09-17/`. The rules checked are the monotone
    rules that fix constants.
    - `2 x 2`: 1296 rules, 4 injective, all layer translations.
    - `M_3`: 816958 rules; `N_5`: 280592; `1 ⊕ (2 x 2)`: 247009; `V`: 25; bowtie: 2. For each of these, exactly 2 are
      injective, and both are copies of one coordinate.
    - The bowtie is not covered by either theorem. The census is only evidence there.
  - What survives.
    - Connected posets where no letter has both meets and joins with every letter: fences, crowns and the bowtie.
      The V shape falls to a direct local sandwich (Remark 2 of the gluing proof, a sketch).
    - Lattices with no product-of-chains glue letter, first `M_3 ⊕ M_3`. Iterating the gluing needs a
      nonincreasing charge at the extreme backgrounds, and none is known. The coatom bound is a nondecrease.
    - Disconnected orders, which include the full conjecture on antichains.
