---
rg: 2
id: bb-kernel-gd-two-if-l-lies-in-contractible-2-complex
kind: claim
title: If a finite flag complex L is a subcomplex of a contractible 2-complex, the Bestvina--Brady kernel H_L has geometric dimension at most 2
distinct_from:
  bestvina-brady-poincare-kernel-has-geometric-dimension-two: that is geometric dimension 2 for the Poincaré spine, where this hypothesis fails by `acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear`; this is a sufficient condition for arbitrary finite flag complexes.
  acyclic-nonaspherical-l-refutes-eilenberg-ganea-or-whitehead: that derives a necessary condition from geometric dimension 2, namely that L is a homotopy retract of a subcomplex of a contractible 2-complex; this is the sufficient condition in which L is itself a subcomplex.
artifacts:
  - research/artifacts/hl-eg-bestvina-brady-2026-09-14.md
---

**ESTABLISHED** through `bb-kernel-gd-two-if-l-in-contractible-2-complex-proof`. Unreviewed.
No novelty is claimed. The plus-construction description of Bestvina--Brady complexes in Howie
(1999) may contain it; its body was not read.

Let `L` be a finite flag complex, `G_L` the right-angled Artin group of its 1-skeleton, and
`H_L` the kernel of `G_L → Z` sending every standard generator to `1`. Suppose there is a
contractible 2-dimensional CW complex `Z` that contains `|L|`, with some CW structure, as a
subcomplex. Then `H_L` acts freely and cellularly on a contractible 2-dimensional CW complex, so
`H_L` has geometric dimension at most 2. If moreover `L` is acyclic and `π_1(L) ≠ 1`, the
geometric dimension equals the cohomological dimension, 2.

## Scope

- **Consequences of the hypothesis.** It forces `H_2(L) = 0` and `H_1(L)` free abelian.
  - Suppose `L` is acyclic with `π_1(L) ≠ 1`. By
    `acyclic-subcomplex-of-contractible-2-complex-pi1-nonhyperlinear`, `π_1(L)` is then not
    hyperlinear.
  - If such an `L` is also non-aspherical, the hypothesis is itself a counterexample to the
    Whitehead conjecture.
  - So the claim is unconditional, but it never applies to acyclic `L` with nontrivial
    hyperlinear `π_1`.
- **Sandwich for acyclic L.** L is a subcomplex of a contractible 2-complex ⇒ gd(H_L) = 2 (this
  claim) ⇒ L is a homotopy retract of a finite subcomplex of a contractible 2-complex (Step 3 of
  `acyclic-nonaspherical-l-dichotomy-proof`).
- **The gap between the two ends.** `bestvina-brady-epsilon-map-conjecture` would upgrade the
  second condition to the first. By `epsilon-map-conjecture-gives-poincare-kernel-gd-three`, that
  upgrade gives geometric dimension 3 whenever `π_1(L)` is nontrivial and hyperlinear.
