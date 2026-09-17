---
rg: 2
id: rest-count-preservation-from-charge-noncreation
kind: route
title: The inverse of a count-monotone reversible automaton never raises the count, so charge noncreation forces equality over every group
target: reversible-automata-that-never-lower-rest-counts-preserve-them
requires:
  - finite-injective-charge-noncreation-forces-surjectivity
---

Complete proof, over every group, with no entropy or soficity input. Notation as in the target: `ψ` is a bijective
cellular automaton on `A^G` with `ψ(a^G) = a^G` and `|ψ(x)| >= |x|` for every finitely supported `x`.

1. **The inverse.** `Φ = ψ^{-1}` is a cellular automaton, by the Curtis–Hedlund–Lyndon theorem: it is a continuous
   equivariant bijection with continuous inverse. It fixes `a^G` and is injective.

2. **Finite configurations.** An automaton fixing `a^G` maps finitely supported configurations to finitely supported
   ones. This applies to both `ψ` and `Φ`.

3. **Nonincrease for `Φ`.** For finitely supported `x`, put `y = Φ(x)`, which is finitely supported by step 2. The
   hypothesis on `ψ` gives `|x| = |ψ(y)| >= |y| = |Φ(x)|`.

4. **Charge noncreation.** Rename `a` as `0` and give every other symbol charge `1`, so `W(x) = |x|` and `0` is the
   unique zero-charge symbol. `Φ` fixes `0^G`, is injective on finitely supported configurations, and satisfies
   `W(Φ x) <= W(x)`. `finite-injective-charge-noncreation-forces-surjectivity` states: "Then equality holds for every
   finite x." So `|Φ(x)| = |x|` for every finitely supported `x`.

5. **Back to `ψ`.** For finitely supported `y`, put `x = ψ(y)`, which is finitely supported by step 2. Then
   `|y| = |Φ(x)| = |x| = |ψ(y)|`.

**Remarks.**
- The countability hypothesis of the target is not used.
- The hypothesis of `count-raising-reversible-automata-lower-biased-rokhlin-entropy` is never satisfied, over any
  group. That hypothesis is an injective automaton fixing `a^G` that never raises the count and lowers it once, and
  step 4 alone rules it out, with no bijectivity needed. Its conclusions are vacuous, and the route `reversible-count-preservation-from-positive-rokhlin-entropy` is
  superseded.
- The star designs described in the target, which move the star set by a reversible automaton, are surjective over
  every group, not only over groups with a positive Rokhlin supremum.
