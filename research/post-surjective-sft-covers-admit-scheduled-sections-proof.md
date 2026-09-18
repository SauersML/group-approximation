---
rg: 2
id: post-surjective-sft-covers-admit-scheduled-sections-proof
kind: route
title: Lift one output site at a time, schedule the lifts by a proper colouring, and colour the Bernoulli shift greedily in Borel fashion
target: post-surjective-sft-covers-admit-scheduled-sections
requires:
  - strict-automaton-lowers-bernoulli-rokhlin-entropy
  - strict-pairs-give-dual-failures-on-bounded-defect-domains
artifacts:
  - research/artifacts/scheduled-sections-of-post-surjective-covers-2026-09-17.md
---

A complete, elementary proof, in Sections 1–5 of the artifact. Proposition C and the reduction lemma are in
Sections 6–7.

1. **Local lift (Lemma 1).** Changing one output letter is liftable inside `gΦ`, by strong post-surjectivity.
   Take the least admissible patch in a fixed order on `A^Φ`. Admissibility reads only `gN`, so the rule is
   local and equivariant.
2. **Separated simultaneous lifts (Lemma 2).** Sites whose mutual differences avoid `E` have write regions `gΦ`
   that are disjoint from each other's read regions `g'N`. Every window and every memory block then meets at most
   one write region, so all such lifts can be done at once.
3. **Schedule (Theorem A).** Run the `|E|` colour classes of a proper colouring in turn, starting from `x_0`.
   Each round fixes its own outputs and leaves the others alone. The result `S(z, κ, x_0)` depends on a finite
   window of the data, so it is continuous and equivariant.
4. **Borel colouring (Lemmas 3–4).** The free part of `B^G` is conull. Greedy colouring along a countable clopen
   basis gives a Borel equivariant proper colouring (Kechris–Solecki–Todorcevic, reproved in full).
5. **Measures (Theorem B).**
   - `Θ(z, w) = (S(z, β(w), ψ(w)), w)` is a Borel equivariant injection with left inverse `F × id`. So the
     pushforward is isomorphic to uniform Bernoulli on `A × B` and misses a cylinder. The ESTABLISHED
     `strict-automaton-lowers-bernoulli-rokhlin-entropy` then gives the deficit.
   - The product base `supp(β_* u) × supp μ` gives the strict measured-controlled automaton.

Both prerequisites are ESTABLISHED.
- `strict-automaton-lowers-bernoulli-rokhlin-entropy` is stated for every invariant measure isomorphic to uniform
  Bernoulli that misses a cylinder. It is used for Theorem B.2 only.
- `strict-pairs-give-dual-failures-on-bounded-defect-domains` is used only for the direction
  (non-surjunctive ⇒ cover pair with a section) of Proposition C.
