---
rg: 2
id: rest-count-preservation-from-charge-noncreation
kind: route
title: The inverse of a count-monotone reversible automaton never raises the count, so charge noncreation forces equality over every group
target: reversible-automata-that-never-lower-rest-counts-preserve-them
requires:
  - finite-injective-charge-noncreation-forces-surjectivity
---

Let `G` be a group, `A` a finite alphabet, `a ∈ A`, and `ψ` a bijective cellular automaton on `A^G` with
`ψ(a^G) = a^G` and `|ψ(x)| >= |x|` for every configuration `x` with finitely many sites outside `a`. No
hypothesis on `G` is used, and no entropy theory.

**Step 1. The inverse is a cellular automaton fixing `a^G`.** `ψ` is a continuous bijection of the compact
Hausdorff space `A^G`, so `τ = ψ^-1` is continuous. It commutes with the shift because `ψ` does. The map
`y ↦ τ(y)(e)` is continuous into the finite set `A`, so it is locally constant. By compactness it is constant
on each of finitely many cylinders fixed by the coordinates in some finite set `M`, so it is `y ↦ f(y|M)` for a
local rule `f`. Equivariance gives `τ(y)(g) = τ(g^-1 y)(e) = f((g^-1 y)|M)`, so `τ` is a cellular automaton.
Also `τ(a^G) = a^G`, because `ψ(a^G) = a^G`.

**Step 2. `τ` maps finite configurations to finite configurations.** Because `τ(a^G) = a^G`, the local rule
sends the all-`a` pattern to `a`. So `τ(y)(g) ≠ a` forces `g M` to meet the finite set of sites where `y ≠ a`.
The same holds for `ψ`.

**Step 3. `τ` never raises the count.** Let `y` be finite and put `x = τ(y)`. By Step 2, `x` is finite. The
hypothesis on `ψ` gives

    |τ(y)| = |x| <= |ψ(x)| = |y|.

**Step 4. Apply charge noncreation.** In `finite-injective-charge-noncreation-forces-surjectivity`, take the
quiescent symbol `0 := a`, with charge `w(b) = 1` for every `b ≠ a` and `w(a) = 0`. Then `W(y) = |y|`. `τ` is a
cellular automaton fixing `a^G` (Step 1). It is globally injective, hence injective on finitely supported
configurations, and `W(τ(y)) <= W(y)` for every finite `y` (Step 3). The imported claim states: "Then equality
holds for every finite x." So `|τ(y)| = |y|` for every finite `y`.

**Step 5. Conclude.** Let `x` be finite and put `y = ψ(x)`, which is finite by Step 2. Step 4 gives
`|x| = |τ(y)| = |y| = |ψ(x)|`.

This closes the claim over every group. Countable infinitude is not needed; for finite `G` the claim is
trivial anyway.

## Consequences for the graph

- **The Rokhlin theorem is vacuous.** Step 4 applied to `Φ` itself shows that no injective automaton fixing
  `a^G` can never raise the count and yet sometimes lower it. That is the hypothesis of
  `count-raising-reversible-automata-lower-biased-rokhlin-entropy`, which is therefore vacuously true. It never
  tied item 15 of `notes/gottschalk-surjunctivity-conjecture-frontier-swarm-2026-09-16.md` to the Rokhlin
  supremum. Its route `reversible-count-preservation-from-positive-rokhlin-entropy` is superseded, and
  `every-group-has-positive-rokhlin-entropy-action` loses this downstream use.
- **Item 15 is dead over every group.** Take a design on `(A ⊔ {*})^G` whose output star set is `ψ(Z)` when
  the input star set is `Z`, for a bijective automaton `ψ` on `{0,1}^G` fixing the all-stars configuration.
  Injectivity on the fibre of configurations with finite nonstar set `Z^c` gives
  `|ψ(Z)^c| >= |Z^c|`, so this claim applies to `ψ` with rest symbol "star". Count preservation makes each fibre
  map a bijection between finite fibres of equal size. So every finite configuration is in the image, the image
  is dense and closed, and the design is surjective. This is the fibre argument of the first consequence of
  `count-raising-reversible-automata-lower-biased-rokhlin-entropy`, now with an unconditional count statement.
- **The gate is creation, not transport.** A strict design with a vacuum must raise every positive charge on
  some finite configuration. Designs that only move or destroy material (charge-nonincreasing, as in item 15,
  or transport-only decoders) are surjective. The deficit computation in
  `experiments/track-deficit-2026-09-17/deficit.py` shows the "information-transport index" of lane (b) is not an
  invariant of reversible composition, so lane (b)'s gate is this creation gate, not a deficit value.

## Concurrent write-up of the same proof

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
