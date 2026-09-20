---
rg: 2
id: noninjective-letter-factors-force-squared-fiber-sizes
kind: claim
title: An injective automaton with a non-injective letter-collapse factor puts the largest fiber size q, qm or q^2 m in NS(G), where m counts the largest fibers
distinct_from:
  collapse-lifts-with-tied-largest-fibers-are-surjective: that needs the base τ injective and concludes q, m or qm fails unless the lift is onto; this needs τ non-injective, allows the lift to be onto, and reduces to that theorem through the fiber-product automaton, whose largest-fiber count is qm, so the third size becomes q^2 m.
  transition-digraph-capacity-lifts-give-nonsurjunctive-sizes: that builds strict lifts whose labels act sitewise, with sizes the monotone capacity sums; this starts from an arbitrary injective lift of an arbitrary base and takes its fiber square, whose labels need not act sitewise.
  ec-groups-share-the-nonsurjunctive-alphabet-sizes: that closes NS(G) under multiples by products with the identity; this uses fiber products over a common base, which multiply fiber profiles pointwise instead of multiplying the alphabet.
  smallest-fiber-collapse-lifts-are-surjective: that needs a bijective base and a unique smallest fiber; this needs a non-injective base and no condition on the profile.
---

**Setting.** `G` is any group and `r : B -> A` is a surjection of finite alphabets with fibers `Q_a = r^{-1}(a)`
and sizes `q_a = |Q_a|`. `Φ` is an injective cellular automaton on `B^G`, and `τ` is a cellular automaton on
`A^G` with `r ∘ Φ = τ ∘ r`. Let `q` be the largest fiber size and `m = |{a : q_a = q}|`. `NS(G)` is as in
`ec-groups-share-the-nonsurjunctive-alphabet-sizes`.

**Theorem.**
1. **(Fiber square.)** On `C = B ×_A B = {(b, b') : r b = r b'}`, which has `Σ_a q_a^2` letters, the
   automaton `Ψ = Φ × Φ` is injective. If `τ` is not injective, or `Φ` is not surjective, then `Ψ` is not
   surjective, so `Σ_a q_a^2 ∈ NS(G)`.
2. **(Squared sizes.)** If `τ` is not injective, then one of `q`, `qm`, `q^2 m` lies in `NS(G)`.
3. **(Letter factors.)** For any injective `Φ` and any letter collapse `r` with a factor `τ`, either `Φ` and
   `τ` are both bijective, or one of `q`, `m`, `qm`, `q^2 m` lies in `NS(G)`.
4. **(Profile products.)** If `Φ_1` and `Φ_2` are injective lifts of the same `τ` through collapses with profiles
   `(q_a)` and `(c_a)`, and `Φ_1` is not onto or `τ` is not injective, then `Σ_a q_a c_a ∈ NS(G)`.

**Consequences.**
- Over a surjunctive group, every letter-collapse factor of an injective automaton is injective. More
  precisely, this holds over any group where none of `q`, `qm`, `q^2 m` fails.
- **Single-letter doubling.** The profile `(2, 1, …, 1)` gives the sizes `2`, `2`, `4`, and `2 ∈ NS(G)` implies
  `4 ∈ NS(G)`. So over a group with `4 ∉ NS(G)`, every injective automaton that commutes with a single-letter
  doubling collapse is bijective, with a bijective base. This holds whatever the base is.
- **The w17 survivor closes.** The survivor "lifts over a non-injective base `τ`" of
  `collapse-lifts-with-tied-largest-fibers-are-surjective` is covered. What remains of the letter-collapse class
  for ascent is the following.
  - Uniform profiles.
  - Designs in which one of the four sizes already fails.
  - Ascents that commute with no letter collapse at all: block-code factors and coupled dynamics.
- **Minimal failing size.** Let `n_0 = min NS(G)`, and let `Φ` be a strict automaton on `n_0` letters with a
  non-uniform letter-collapse factor `τ`. Then `τ` is not injective, and `q^2 m ∈ NS(G)` with `q^2 m >= n_0`.
  The reason: `q`, `m` and `qm` are all below `n_0`, and w17 excludes an injective base.
