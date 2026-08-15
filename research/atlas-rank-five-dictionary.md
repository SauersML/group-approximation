---
rg: 2
id: atlas-rank-five-dictionary
kind: claim
title: All one hundred rank-five Steinberg generators are explicit atlas words, exactly verified
distinct_from:
  atlas-steinberg-rank-five-translation: that is the full usable-list program; this is its Step 2, now complete — the factorization dictionary alone, with the presentation-completeness input still open there.
  atlas-charts-overlap-trivially: that proved the charts share no subgroup and flagged the uniform-refinement trap; this shows the trap is irrelevant to factorization — the join code works because the criterion needs words in K₁ ∪ K₂, not chart containment.
artifacts:
  - research/artifacts/atlas-rank5-dictionary-2026-08-15.md
  - experiments/atlas_relator_rank5_dictionary.py
---

Take the **join** of the two atlas charts as the rank-five prefix code:

```text
E = (000, 001, 010, 011, 1) = (γ₁e, γ₁f, γ₂e, γ₂f, γ₃)
```

over the rank-three code `γ = (00, 01, 1)`.  `E` is a complete prefix code
of size five, so `Θ_E` gives `E₅(L) ≅ Q` and the hundred generators
`x_kl(b) = 1 + E_k b E_l^*`, `k ≠ l`, `b ∈ {1, e, f, e^*, f^*}`.

**Theorem (machine-verified exact computation).**  Every `x_kl(b)` is an
explicit word in the twelve adjacent-transvection atlas generators: all
100 were built and verified exactly against `1 + E_k b E_l^*` by binary
Leavitt arithmetic, with syllable lengths 1–17 and X-lengths 1–92 (3,412
letters in total).

**Mechanism.**  With `p(k)` the rank-three parent of `E_k` and `s_k` its
suffix (`p = (1,1,2,2,3)`, `s = (e,f,e,f,–)`):
`E_k b E_l^* = γ_{p(k)} (s_k b s_l^*) γ_{p(l)}^*`.

- **Case A** (`p(k) ≠ p(l)`, 80 generators): the target lies in the
  abelian root subgroup `U_{ij}(c)`, `c = s_k b s_l^*` a product of at
  most three letters, never zero (the letter pattern
  `[unstarred][b][starred]` admits no annihilating adjacency).  Iterating
  `[U_{ik}(a), U_{kj}(b)] = U_{ij}(ab)` over the three rank-three indices
  reaches every such `c` from the thirty already-explicit rank-three
  generators.
- **Case B** (`p(k) = p(l)`, 20 generators): route through index five,
  `x_kl(b) = [x_{k5}(b), x_{5l}(1)]`.  Index 5 is the leaf `γ₃` — the one
  leaf the two charts share — and it is the hinge of the entire
  dictionary.

**Why the uniform-refinement trap does not bite.**  `E` refines `D₁, D₂`
non-uniformly, so `GL(E)` contains neither chart group
(`atlas-charts-overlap-trivially`) — but the criterion needs each
`x_kl(b)` to be a *word* in `K₁ ∪ K₂`, not to lie in a chart.  The trap
blocks chart-containment, not factorization.

**What this completes.**  Step 2 of `atlas-steinberg-rank-five-translation`
— the step its program called "the real work".  Translating the rank-five
Steinberg/Cuntz–Krieger relation family through this dictionary already
produces verified kernel words escaping the cartesian subgroup, in
agreement with `atlas-kernel-window-length-nine` (11 of 83 in the smoke
run have nontrivial factor projections); the sole remaining input for a
usable relator list is completeness of that family as a presentation of
`St₅(L)` over the finite ring presentation of `L`.
