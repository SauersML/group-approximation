---
rg: 2
id: count-raising-reversible-automata-lower-biased-rokhlin-entropy
kind: claim
title: A reversible binary automaton that never lowers and sometimes raises the number of zeros lowers biased Bernoulli Rokhlin entropy
distinct_from:
  passive-fixing-injective-automata-are-surjective: that proves surjectivity when reserved symbols stay in place, with no condition on the group; this lets the reserved set move under a reversible automaton and turns a gain in its complement into an entropy deficit of a biased Bernoulli shift.
  strict-automaton-lowers-bernoulli-rokhlin-entropy: that starts from a strict automaton and bounds the Rokhlin entropy of amplified uniform shifts; this starts from a bijective automaton, which is not strict, and bounds the Rokhlin entropy of biased coin shifts at small bias.
  bijective-ca-preserve-uniform-bernoulli-measure: that is invariance of the uniform product measure under reversible automata; this is a strict change in the zero density of product measures of small bias under the inverse of a count-raising reversible automaton.
  bernoulli-rokhlin-entropy-maximal-for-every-group: that is the open maximality of uniform Bernoulli Rokhlin entropy; this proves that a count-raising reversible automaton refutes maximality for the biased coins `(p, 1 - p)` with `p` small.
---

**ESTABLISHED** by `count-raising-reversible-automata-rokhlin-deficit-proof`.

Let `G` be a countably infinite group and `ψ` a bijective cellular automaton on `{0,1}^G` with `ψ(1) = 1`,
where `1` is the all-ones configuration. For a configuration `x` with finitely many zeros write `|x|` for the
number of zeros. Suppose that `|ψ(x)| >= |x|` for every such `x`, with strict inequality for at least one.
Let `μ_p` be the product measure with `μ_p(x(g) = 0) = p`. Then there are `m >= 1`, `c > 0` and `p_0 > 0`
such that for every `0 < p < p_0`:

- `μ_p(ψ^-1(x)(1_G) = 0) = p - c p^m + O(p^(m+1)) < p`;
- `h^Rok_G({0,1}^G, μ_p) <= H(p - c p^m + O(p^(m+1))) < H(p)`, where `H` is binary Shannon entropy.

**Consequences.**
- **Groups with maximal biased Bernoulli entropy.** If `h^Rok_G(μ_p) = H(p)` for arbitrarily small `p > 0`,
  every bijective automaton on `{0,1}^G` fixing `1` that never lowers the number of zeros preserves it. This
  holds for sofic groups, and for every group with an infinite Rokhlin entropy supremum
  (`infinite-rokhlin-supremum-forces-surjunctivity`, item 1).
- **Autonomous star designs.** Let `C = A ⊔ {*}` with `A` nonempty, and let `Φ` be an injective automaton on
  `C^G` whose output star set is `ψ(Z)` whenever the input star set is `Z`, for a bijective automaton `ψ` on
  `{0,1}^G` fixing the all-stars configuration. Injectivity on the finite set of configurations with a given
  finite non-star set `W` gives `|ψ(W)^c| >= |W^c|`. If the count is preserved, `Φ` maps those `|A|^|W|`
  configurations injectively, hence onto, the configurations with non-star set `ψ(W)^c`. The image then
  contains every configuration with finitely many non-star sites, which are dense, and it is closed. So `Φ`
  is surjective. Hence a strict autonomous star design over `G` forces `h^Rok_G(μ_p) < H(p)` for all small
  `p`. This settles item 15 of `notes/gottschalk-surjunctivity-conjecture-frontier-swarm-2026-09-16.md` up
  to the entropy barrier: the class is no easier to realize than a biased Bernoulli entropy deficit.
- **Unconditional low counts.** Over every group such a `ψ` keeps the number of zeros whenever it is 1 or 2
  (proof, part B). The first count that can rise is at least 3.

**Scope.** No group is excluded unconditionally. The measure argument sees only the lowest order at which
`ψ^-1` lowers counts, so it gives nothing about the uniform measure, where density is preserved
(`bijective-ca-preserve-uniform-bernoulli-measure`).
