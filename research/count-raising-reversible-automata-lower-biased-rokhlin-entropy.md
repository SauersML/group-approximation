---
rg: 2
id: count-raising-reversible-automata-lower-biased-rokhlin-entropy
kind: claim
title: An injective automaton that never raises and sometimes lowers the number of non-rest sites forces Rokhlin supremum zero
distinct_from:
  passive-fixing-injective-automata-are-surjective: that proves surjectivity when reserved symbols stay in place, with no condition on the group; this lets the rest symbol move and turns a loss in its complement into a vanishing Rokhlin supremum.
  strict-automaton-lowers-bernoulli-rokhlin-entropy: that starts from a strict automaton and bounds the Rokhlin entropy of amplified uniform shifts; this starts from a count condition, which bijective automata can satisfy, and bounds the Rokhlin entropy of small-bias shifts.
  strict-automaton-bounds-rokhlin-supremum: that gets a finite supremum from a strict automaton; this gets supremum zero from a count-lowering injective automaton, with no hypothesis on self-copies or finite subgroups.
  bijective-ca-preserve-uniform-bernoulli-measure: that is invariance of the uniform product measure under reversible automata; this is a strict drop in the non-rest density of product measures of small bias.
  bernoulli-rokhlin-entropy-maximal-for-every-group: that is the open maximality of uniform Bernoulli Rokhlin entropy; this refutes maximality at every finite base over any group carrying a count-lowering injective automaton.
artifacts:
  - experiments/count-charge-mobius-2026-09-17/check.py
---

**ESTABLISHED** by `count-raising-reversible-automata-rokhlin-deficit-proof`.

Let `G` be a countably infinite group, `A` a finite alphabet with `k = |A| >= 2`, and `a ∈ A` a *rest* symbol.
For a configuration `x` with finitely many sites outside `a`, write `|x|` for the number of those sites. Let
`Φ` be an injective cellular automaton on `A^G` with `Φ(a^G) = a^G`. Suppose that `|Φ(x)| <= |x|` for every such
`x`, with strict inequality for at least one. Let `μ_p` be the product measure in which a site is `a` with
probability `1 - p`, and otherwise a uniform symbol of `A \ {a}`. Then:

1. There are `m >= 1` and `c > 0` such that `μ_p(Φ(x)(1_G) ≠ a) = p - c p^m + O(p^(m+1))`.
2. For all small `p > 0`, `h^Rok_G(A^G, μ_p) < H(p) + p log(k - 1)`, the base entropy.
3. `h^Rok_sup(G) = 0`. So every Bernoulli shift over `G` with finite base entropy has Rokhlin entropy `0`, and `G`
   is not sofic.

**Reversible form.** Let `ψ` be a bijective automaton on `A^G` fixing `a^G` with `|ψ(x)| >= |x|` for all
finitely supported `x`, and strict inequality for some. Its inverse restricts to a bijection of the finitely
supported configurations and satisfies the hypothesis, so `h^Rok_sup(G) = 0`. Over every group, a binary such `ψ`
keeps the count whenever it is 1 or 2 (proof, part B).

**Consequences.**
- **Autonomous star designs.** Let `C = A ⊔ {*}` with `A` nonempty, and let `Φ` be an injective automaton on
  `C^G` whose output star set is `ψ(Z)` whenever the input star set is `Z`, for a bijective automaton `ψ` on
  `{0,1}^G` fixing the all-stars configuration.
  - Injectivity on the finite set of configurations with a given finite non-star set `W` gives
    `|ψ(W)^c| >= |W^c|`.
  - If the count is preserved, `Φ` maps those `|A|^|W|` configurations injectively, hence onto, the configurations
    with non-star set `ψ(W)^c`. The image then contains every configuration with finitely many non-star sites.
    These are dense and the image is closed, so `Φ` is surjective.
  - Otherwise the reversible form applies to `ψ`.

  So a strict autonomous star design over `G` forces `h^Rok_sup(G) = 0`. That is item 15 of
  `notes/gottschalk-surjunctivity-conjecture-frontier-swarm-2026-09-16.md`, settled up to the Rokhlin barrier.
- **Comparison with strictness.** A strict automaton only gives a finite supremum
  (`strict-automaton-bounds-rokhlin-supremum`). The count condition gives supremum `0` directly. So on any group
  with a free ergodic action of positive, finite Rokhlin entropy, no such `Φ` or `ψ` exists.

**Scope.** No group is excluded unconditionally, because it is open whether `h^Rok_sup(G) > 0` for every group. The
measure argument sees only the lowest order at which the count drops.
