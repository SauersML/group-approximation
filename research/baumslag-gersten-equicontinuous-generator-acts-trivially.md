---
rg: 2
id: baumslag-gersten-equicontinuous-generator-acts-trivially
kind: claim
title: In any action of the Baumslag--Gersten group on a compact zero-dimensional metrizable space in which the powers of a are equicontinuous, a acts trivially
distinct_from:
  baumslag-gersten-odometer-pieces-force-fixed-points: that shows that a b-invariant minimal equicontinuous piece of a forces a fixed point of a, on any compact metrizable space; this uses zero-dimensionality to conclude that an equicontinuous a acts trivially on the whole space.
  baumslag-gersten-group-is-neither-linear-nor-self-similar: that shows that every finite image of BG kills a; this is the profinite version for compact zero-dimensional actions with equicontinuous a, and recovers it when the space is finite.
artifacts:
  - research/artifacts/bh-bg-similarity-hosts-2026-09-12.md
---

**ESTABLISHED** (elementary; no novelty claimed).

**Statement.** Let `BG = < a, t | b a b^-1 = a^2 >`, where `b = t a t^-1`.
Suppose `BG` acts by homeomorphisms on a compact zero-dimensional metrizable
space `X`, and `{a^m : m ∈ Z}` is equicontinuous. Then `a` acts as the
identity.

**Consequences.**
- In any embedding of `BG` in the homeomorphism group of a Cantor space, the
  image of `a` is not equicontinuous.
- If `X` is finite, this says that every finite image of `BG` kills `a`.

**Sharpness.**
- The stable letter `t` is needed. `BS(1,2) = < a, b >` acts faithfully on
  `Z_3` by `x ↦ x+1` and `x ↦ 2x`, and there `a` is an isometry.
  - The closures of `<a>` and `<b>` are then `Z_3` and `Z_3^×`.
  - These have different prime sets, so they are not conjugate.
- Zero-dimensionality is used only to make the closure of `<a>` profinite.

The proof is `baumslag-gersten-equicontinuity-smallest-prime-proof`.
