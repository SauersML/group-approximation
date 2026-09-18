---
rg: 2
id: constant-point-domains-via-bernoulli-rokhlin-maximality
kind: route
title: Section a constant-point cover over a Borel colouring of the Bernoulli shift and read off a Rokhlin deficit
target: constant-point-sft-domains-admit-no-post-surjective-covers
requires:
  - post-surjective-sft-covers-admit-scheduled-sections
  - bernoulli-rokhlin-entropy-maximal-for-every-group
artifacts:
  - research/artifacts/scheduled-sections-of-post-surjective-covers-2026-09-17.md
---

Suppose `X ⊊ A^G` is an SFT that contains a constant `c`, and `F : X → A^G` is strongly post-surjective with lifts
in `X`.
1. **Reduce the group.** By Lemma 5 of the artifact, the same local data give a counterexample over
   `H = ⟨W ∪ M ∪ Φ⟩`, and `H` is infinite. So assume `G` is countably infinite.
2. **Deficit.** By Theorem B.2–3 of `post-surjective-sft-covers-admit-scheduled-sections` (constant variant,
   `Θ(z) = S(z, β(z), c)`), the uniform Bernoulli shift over `G` with alphabet `A^k` has Rokhlin entropy below
   `k log |A|` for large `k`.
3. **Contradiction.** That contradicts `bernoulli-rokhlin-entropy-maximal-for-every-group` for the alphabet `A^k`.

**What this adds.** `gottschalk-via-maximal-bernoulli-rokhlin-entropy` already derives Gottschalk from the same
hub. This route shows that the constant-point step of `gottschalk-via-constant-point-domains` is no stronger than
that hub. The same holds per group: Rok-max(G) ⇒ CP(G) ⇒ surjunctive(G). So CP is an intermediate statement, no harder
than the Rokhlin hub. No converse (CP ⇒ Rok-max) is known.

The same argument with Theorem B.1 in step 2 gives MCS(G) ⇒ CP(G), for measured-controlled surjunctivity as in
`measured-controlled-surjunctivity-is-envelope-invariant`. No route is filed for that, because no node asserts MCS
for every group.
