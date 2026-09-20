---
rg: 2
id: monotone-injective-automata-on-connected-posets-are-surjective
kind: claim
title: Over every group, a monotone injective automaton on a connected finite poset alphabet is surjective
distinct_from:
  monotone-automata-with-a-pinned-bracketing-star-are-onto: that proves the statement when one letter has a rigid star bounding every letter; this is the full connected case, open first at the six-letter fence and the six-letter crown.
  monotone-strict-automata-ascend-along-poset-homs: that is the ascent whose connected survivors this would kill all at once.
  monotone-injective-chain-automata-are-translations: that is the chain case.
artifacts:
  - experiments/monotone-connected-posets-2026-09-17/search_z.py
  - experiments/monotone-connected-posets-2026-09-17/search_z_results.txt
---

**OPEN.**

**Conjecture.** Let `G` be any group and `L` a finite poset whose comparability graph is connected. Every injective
automaton on `L^G` that is monotone (`x <= x'` sitewise implies `ρ(x) <= ρ(x')`) is surjective.

**Why it matters.** By `monotone-strict-automata-ascend-along-poset-homs`, a monotone strict automaton on `L` would
put every count `|Hom(P,L)|` into `NS(G)`. After chains and the component reduction there, the connected non-chains
are what survives. This conjecture kills the whole order-theoretic ascent on connected alphabets.

**Known cases.**
- Chains: `monotone-injective-chain-automata-are-translations`.
- One letter has a rigid (pinned) up-set that bounds every letter from above, or the dual. This covers `K_{p,q}`,
  `N`, fences of at most five letters, and posets with a top and a minimal letter whose up-set is a chain:
  `monotone-automata-with-a-pinned-bracketing-star-are-onto`.
- Reported on the bus by swarm-0917 gs-alt, not landed in this worktree: products of chains (each layer moves by its
  own translation), and lattices glued at a letter with chain-product ideal and filter (`M_n`, `N_5`).
- Census over `Z`, window 2 (artifact): on ten connected posets every monotone injective rule is a product of
  coordinate copies.

**First open cases.** The fence `a1 < c1 > m1 < c2 > m2 < c3` of six letters, longer fences, and crowns `C_{2k}` with
`k >= 3`. Also, over every group, any poset with no letter whose star reaches every letter.

## Attempts

**2026-09-19, swarm-0917 gs-follow: one preserved letter (bracketing).** Normalize `ρ` to fix constants. In a
connected height-one poset, all cover translations are equal: two covers that share a bottom `m` meet inside the
pinned star `↑m = ⊥ + A`, and dually for a shared top, so connectivity propagates one label. After composing with
the inverse translation, `ρ` is the identity on every star `(↑m)^G` and `(↓c)^G`. A letter is *preserved* when it
can be bracketed by a configuration inside a star. Item 1 of `monotone-automata-with-a-pinned-bracketing-star-are-onto`
then gives surjectivity. It also gives "iff", which removes that letter from every other letter's range.
- *Where it dies.* An upper bracket for `x(h) = m` must dominate `x` at every site of the window `hM`. So every
  letter of `L` needs a common upper bound with `m` inside one pinned subalphabet. In the six-letter fence
  `a1 < c1 > m1 < c2 > m2 < c3`, no star contains an upper bound of both `a1` and `c3`, and none contains a lower
  bound of both. A window holding `a1` and `c3` is bracketed by nothing known. The same holds in every crown
  `C_{2k}` with `k >= 3`.

**2026-09-19, swarm-0917 gs-follow: leaf deletion (sketch, not written as a route).** Brackets need not be
order-preserving letter maps. Any sitewise raise or lower works, because only `e <= x` is used.
- *Extension step.* Let `z` and `w` be distinct leaves of a height-one `L`. Suppose `(L∖{z})^G` and `(L∖{w})^G`
  are invariant and `ρ` is the identity on both. Then `ρ = id`.
  - Lowering (or raising) every `z` to its neighbour `n` gives a bracket in `(L∖{z})^G`. It preserves every letter
    except `n` and `z`, and iff removes those letters from the other ranges.
  - The same with `w` leaves at most the common neighbour. Elimination settles that neighbour.
- *Invariance.* For `a1 < c1 > m1 < c2 > m2 < c3`, the subshift `(L∖{c3})^G` is invariant. Raise `y` to a
  configuration over `{c1, c2}`. That configuration dominates `m1^G`, so its image lies in `↑m1 ∌ c3`. The same
  holds for `(L∖{a1})^G`: lower to `{m1, m2}^G <= c2^G`.
- Together with fence5 pinned, which is proved the same way from the invariant `N`-subalphabet `L∖{a2}`, this pins
  the six-letter fence. So `fence6` is almost certainly killed, but only as a sketch.
- *Where it dies.* Invariance of `(L∖{z})^G` needs the tops other than `z` to share a lower letter, or dually the
  bottoms to share an upper letter. The fence of seven or more letters has no such leaf. Crowns have no leaves at all.

**2026-09-19, swarm-0917 gs-follow: Hasse-distance charge (reduction, open).** *Claim C*: if `x` and `x'` differ at
one site by a cover, then `ρ(x)` and `ρ(x')` differ at exactly one site, by a cover.
- Claim C implies the conjecture. Fix a quiescent letter `q` and put `W(x) = Σ_h d(q, x(h))`, with `d` the distance
  in the Hasse graph. Walk from `q^G` to a finite `x` in `W(x)` single-site cover steps. Each step moves
  `W(ρ·)` by at most 1, so `W(ρx) <= W(x)`, and charge noncreation gives surjectivity.
- The census checks Claim C on every context of every injective rule found: 0 violations.
- *Where it dies.* Monotonicity only says that the changed sites move up (or down). It does not bound how many sites
  change. Injectivity controls this only through the global charge, so the step is circular.

**2026-09-19, swarm-0917 gs-follow: pinning is the wrong induction invariant.** The Boolean square is connected but
not pinned: `(y,z) ↦ (y_t, z_{t'})` with `t != t'` is monotone and bijective. So any proof that makes all cover labels
equal must fail on products. Labels can only be constant on classes of parallel covers, the `Θ`-classes of the
cover graph. A general proof must work per class: per-class translations, then charge noncreation per class.
