---
rg: 2
id: core-permutation-models-extend-to-folding-acts
kind: claim
title: Separating permutation models of the core table group extend to dense folding act certificates on the non-core letters
distinct_from:
  folding-act-certificates-reduce-to-core-permutation-models: that proves folding certificates restrict to core permutation models; this asks for the converse extension from core models to full acts.
  sofic-radical-localizes-garden-of-eden-windows: that localizes strict windows to invisible elements of the memory group; this would sharpen the localization to core words in the core table group B(D,E).
artifacts:
  - research/artifacts/folding-act-certificates-2026-09-17.md
---

**OPEN.** Let `(D, E, W)` be a design, a forward-sufficient partition and a Garden-of-Eden
window datum. Suppose there is `δ > 0` such that almost-multiplicative permutation models of
`B(D,E)`, with defect tending to 0, move the core word of every core-expressible distinguished
pair at density at least `δ`. Then there are act models with slack `o(|V|)` and
`|U_1| >= δ'|V|` for some `δ' > 0`.

**Payoff.** Combined with `folding-act-certificates-reduce-to-core-permutation-models`, a strict
design would force some distinguished pair to be core-expressible with an invisible core word.
This replaces `Rad(<M>)` by the sofic radical of the finitely presented `B(D,E)` in
`sofic-radical-localizes-garden-of-eden-windows`. A design with trivial core propagation would
be non-strict.

**Where it can fail on its own.**
- Non-core letters sit on cycles of relators that impose `a_m ∘ pi = a_m` or `b_s = pi ∘ b_s`
  for core words `pi`.
- Absorbing such a relation folds `a_m` along `pi`-orbits. This can merge distinguished
  outputs that are not core-expressible.
- The constant fold of Proposition C does merge them, so the extension must be non-constant.

Section 5 of the artifact states the problem.

## Attempts

- **Absorbing point fold (a-gs-pull-2, 2026-09-17).**
  - **Structural fact:** by (C2), an `E`-class that contains one fully core pair is fully core.
    Every other class has a non-core letter in each of its pairs.
  - **Construction:** add a point `u*` to `U` and `v*` to `V`. Make every non-core `b_s` constant
    `u*` and every non-core `a_m` constant `v*`. Extend the core letters by `a_m(u*) = v*` and
    `b_s(v*) = u*`.
  - **Result:** every site that is good for the core model stays good, since non-core classes
    all evaluate to `v*`. The slack is unchanged, because both layers gained one point.
  - **Where it dies: window-goodness.**
    - A `Pi`-class that mixes a core letter `m` with a non-core letter forces `g_w u = u*` for
      its `w`. Two such `w` with different `p`-values merge a distinguished pair.
    - Along all-core `Pi`-classes, the points `iota g_w u` must satisfy the chain equations at
      once. That needs the core words of `Pi`-cycles to act almost trivially at window points.
      The hypothesis above does not supply this, since those words need not be relators of
      `B(D,E)`.

  So the claim as stated needs either a finer fold on mixed `Pi`-classes or a strengthened
  hypothesis that includes `Pi`-cycle words. Both are recorded, and neither is settled.
