---
rg: 2
id: post-surjective-automata-never-enlarge-the-alphabet
kind: claim
title: No strongly post-surjective automaton maps a full shift onto a full shift over a strictly larger alphabet
distinct_from:
  full-shifts-with-different-alphabets-are-not-conjugate: that forbids equivariant injections that shrink the alphabet, which is settled by counting constants; this forbids strongly post-surjective automata that enlarge it, where constants give no obstruction because the map need not hit them.
  every-group-is-dual-surjunctive: that asks every post-surjective self-map of one full shift to be pre-injective; this is the two-alphabet rank statement, which follows from it by alphabet-enlarging-covers-refute-dual-and-domain-duality and is not known to imply it.
  constant-point-sft-domains-admit-no-post-surjective-covers: that forbids covers from any proper SFT with a constant; this is its special case where the domain is the full shift on a subalphabet, and every such cover has D ≠ ∅, so it is off the Gottschalk route.
  proper-sft-domains-admit-no-dual-failures: that concerns strongly irreducible SFT domains and concludes pre-injectivity; this concerns only full-shift domains and concludes non-existence.
  nonsurjunctive-alphabet-sizes-are-upward-closed: that concerns injective self-maps and changes of alphabet size for strictness; this concerns post-surjective maps between two different alphabets.
artifacts:
  - research/artifacts/fixed-point-surjectivity-and-free-monoid-calibration-2026-09-18.md
---

**OPEN.** Read group by group. Let `G` be a group and `A`, `B` finite alphabets with `|B| > |A|`. There is no
automaton `P : A^G → B^G` that is strongly post-surjective in the sense of
`strict-pairs-give-dual-failures-on-bounded-defect-domains` (a finite `Φ ⊆ G` with: for all `x` and all
`z ~ P(x)` there is `x' ~ x` with `P(x') = z` and `Δ(x, x') ⊆ Δ(P(x), z)Φ`).

Call this NPE(G), for "no post-surjective expansion". It is the rank condition for automata: a surjection of
free `F[G]`-modules `F[G]^m → F[G]^n` forces `m ≥ n`, and NPE asks the same of nonlinear strongly
post-surjective maps.

**Known cases.**
- Sofic `G` (so amenable and residually finite `G`): NPE(G) holds, because sofic groups are dual surjunctive
  (Doucha–Gismatullin) and dual surjunctivity implies NPE, by part 1 of
  `alphabet-enlarging-covers-refute-dual-and-domain-duality`.
- Linear automata over a finite field `F`, with `A = F^m`, `B = F^n`: NPE holds for every group, by part 5 of
  the same claim. The trivial module kills the group.
- Monoids: false. On the free monoid `M = {a, b}*`, the map `P(x)(w) = (x(wa), x(wb))` from `A^M` to
  `(A × A)^M` is strongly post-surjective with `Φ = {a, b}`. The lift sets `x'(ua) = z(u)_1`, `x'(ub) = z(u)_2`
  and keeps `x'(ε)`. This is the paradoxical input `Ma ⊔ Mb = M \ {ε}` of the calibration artifact, §4. So a
  proof of NPE must use invertibility of translations.

**Why it matters.** By `alphabet-enlarging-covers-refute-dual-and-domain-duality`, a counterexample `P` at `G`
refutes, at `G`, all three of `every-group-is-dual-surjunctive`,
`constant-point-sft-domains-admit-no-post-surjective-covers` and `proper-sft-domains-admit-no-dual-failures`.
It does not touch `gottschalk-surjunctivity-conjecture` through any recorded route. Every dual failure or
cover pair built from `P` misses a constant, so it has no section and no automaton right inverse. So NPE is a
common core of the three duality statements that lies outside the fragment the Gottschalk routes consume.

**How it could fail.** A non-sofic `G` with a "paradoxical reading" automaton, as in the monoid example, but
with invertible translations. Over a group, an automaton with a one-element memory `{s}` is a letter map
`A → B` composed with the homeomorphism `x ↦ (g ↦ x(gs))`, so it is not onto `B^G`. A counterexample needs a
memory with at least two elements.
