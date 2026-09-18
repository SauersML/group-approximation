---
rg: 2
id: post-surjective-sft-covers-admit-scheduled-sections
kind: claim
title: A strongly post-surjective cover of a proper SFT has a continuous section over the proper-colouring shift, so it forces a Bernoulli Rokhlin deficit and a strict measured-controlled automaton
distinct_from:
  constant-point-sft-domains-admit-no-post-surjective-covers: that forbids such covers of constant-point domains outright; this proves that any such cover has a section once a proper colouring is supplied, and so derives that claim at G from Bernoulli Rokhlin maximality or from measured-controlled surjunctivity at G.
  strict-automaton-lowers-bernoulli-rokhlin-entropy: that turns an injective map into a proper subshift into a Rokhlin deficit; this manufactures such a Borel injection from a strongly post-surjective cover, with no cellular automaton on the full shift.
  proper-sft-covers-exclude-finite-orbits-and-sofic-constants: that counts fixed points on finite quotients or sofic models; this uses no finite model and works on every group, at the price of an entropy or measured-controlled hypothesis.
  compressible-base-controlled-automata-are-strict: that builds strict controlled automata over bases with no invariant measure; this builds them over a colouring base with a Bernoulli-type invariant measure, with a decoder that does not depend on the base.
  nonamenable-groups-carry-arrow-shift-strict-automata: that fibres a hotel map over an arrow shift, which carries no invariant measure; this fibres a section over the proper-colouring shift, which carries one.
artifacts:
  - research/artifacts/scheduled-sections-of-post-surjective-covers-2026-09-17.md
---

**ESTABLISHED (unreviewed)** by [[post-surjective-sft-covers-admit-scheduled-sections-proof]].

**Setting.**
- `G` is a group and `A` a finite alphabet, `|A| = q >= 2`.
- `X ⊊ A^G` is an SFT and `F : X → A^G` an automaton. `F` is strongly post-surjective with lifts in `X`, as in
  `strict-pairs-give-dual-failures-on-bounded-defect-domains`. Call `(X, F)` a **cover pair**.
- `E = NΦ^-1 ∪ ΦN^-1 ∪ {1}`, where `N = ΦW^-1W ∪ ΦM^-1M`; `W` is the window of `X`, `M` the memory of `F` and `Φ`
  the lift constant. `C ⊆ [|E|]^G` is the shift of proper colourings of the Cayley graph of `E`.

**Theorem A (scheduled sections, every group).** Lift one site at a time by a fixed local rule, run the colour
classes of `κ ∈ C` in order, and start from any `x_0 ∈ X`. The result is a continuous equivariant
`S : A^G × C × X → X` with `F(S(z, κ, x_0)) = z`. For any zero-dimensional compact base `Ω` with continuous
equivariant maps `Ω → C` and `Ω → X`, the map `(z, ω) ↦ (S(z, κ(ω), ξ(ω)), ω)` is a strict `Ω`-controlled
automaton:
- every fibre is injective;
- no fibre is surjective;
- the decoder `F` does not depend on the base.

**Theorem B (every countably infinite group).** Let `(X, F)` be a cover pair.
1. If `X` carries an invariant probability, then `G` is not measured-controlled surjunctive (MCS, as defined in
   `measured-controlled-surjunctivity-is-envelope-invariant`). The base is `supp(β_* u_A) × supp μ`, where `β` is
   a Borel proper colouring of the free part of the Bernoulli shift.
2. Suppose `X` carries a point that is a Borel factor of a uniform Bernoulli shift `B^G`. Then some amplified
   uniform Bernoulli shift over `G` has Rokhlin entropy below its base entropy, with the explicit bound of
   `strict-automaton-lowers-bernoulli-rokhlin-entropy` for the alphabet `A × B`.
3. A constant configuration in `X` is such a point, and `δ_c` is such a measure.

**Consequences.**
- Per countably infinite group, Bernoulli Rokhlin maximality (all alphabets) implies
  `constant-point-sft-domains-admit-no-post-surjective-covers` (CP), and so does MCS. With Lemma 5 of the artifact
  (reduction to finitely generated subgroups), `bernoulli-rokhlin-entropy-maximal-for-every-group` gives CP for all
  groups: route `constant-point-domains-via-bernoulli-rokhlin-maximality`.
- CP lies between the Rokhlin hub and Gottschalk:
  - Rok-max(G) ⇒ CP(G) ⇒ surjunctive(G);
  - MCS(G) ⇒ CP(G).
- The stronger exclusion is also proved: no cover pair carries a Bernoulli-factor point. This covers cover pairs
  with no finite orbit at all.
- **Proposition C.** `G` is not surjunctive iff some cover pair (with a constant point) has a continuous
  equivariant section `A^G → X`. So for surjunctive `G`, CP(G) says exactly that every constant-point cover pair
  can be de-coloured. The colouring cannot be dropped for free: at a constant target, a section must return a
  point with the full symmetry, and a colouring has none (artifact Section 6).

Nothing here decides CP at any nonsofic group.
