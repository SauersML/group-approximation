---
rg: 2
id: baumslag-gersten-odometer-fixed-point-proof
kind: route
title: On a minimal rotation of a compact monothetic group the relation b a = a^2 b forces b to be x -> c + 2x, which fixes -c; conjugate the fixed point back by t
target: baumslag-gersten-odometer-pieces-force-fixed-points
requires: []
artifacts:
  - research/artifacts/bh-baumslag-gersten-2026-09-12.md
---

**Item 1.**
- **Model.** A minimal equicontinuous homeomorphism of a compact metrizable
  space is conjugate to a minimal rotation `x ↦ x + θ` of a compact abelian
  metrizable monothetic group `K`, with `Zθ` dense. This is the standard
  structure theorem for equicontinuous minimal systems (e.g. Auslander,
  *Minimal Flows and their Extensions*, Chapter 3). Identify `Y` with `K` and
  `a|Y` with `x ↦ x + θ`.
- **The relation.** `b a b^-1 = a^2` gives `b ∘ a = a^2 ∘ b` on `Y`, which `b`
  preserves. So `b(x + θ) = b(x) + 2θ`.
- **Iteration.** By induction, and using `a^-1` for negative `n`,
  `b(x + nθ) = b(x) + 2nθ` for all `n ∈ Z`.
- **Continuity.** For `k ∈ K` choose `n_j θ -> k`. Since `b`, translation and
  `x ↦ 2x` are continuous, `b(x + k) = b(x) + 2k`. At `x = 0`, with
  `c = b(0)`, this gives `b(k) = c + 2k` for all `k ∈ K`.
- **Fixed point.** `b(-c) = c - 2c = -c`, so `y = -c` is a fixed point of `b`.
- **Transfer.** `b = t a t^-1`, so `a = t^-1 b t` and
  `a(t^-1 y) = t^-1 b(y) = t^-1 y`.

**Item 2.** Take `Y = X`. A minimal homeomorphism of a space with at least two
points has no fixed point, since the orbit closure of a fixed point is that
point. Item 1 gives `a` a fixed point in `X`. Contradiction.

**Item 3.**
- **Affine ternary model.** `Z[1/2] ⊆ Z_3` and `2 ∈ Z_3^x`. The affine maps
  `x ↦ 2^k x + r`, with `r ∈ Z[1/2]`, form a copy of `BS(1,2)`, and
  `b a b^-1 (x) = 2(x/2 + 1) = x + 2`.
- **Faithfulness.** A translation by `r ≠ 0` moves every point, and the maps
  with `k ≠ 0` are not translations.
- **Self-similarity.** If `x ∈ Z[1/2]` and `x ≡ d (mod 3 Z_3)`, then
  `(x - d)/3 ∈ Z[1/2]`, because `3 ∤ 2^j`. So the sections of these maps on the
  cylinders `d + 3Z_3` are again of this form.
- **Adding machine.** `x ↦ x + 1` is minimal and equicontinuous on `Z_3`, so
  item 2 applies with `X = Y = Z_3`. For a proper invariant piece `Y ⊊ X` that
  `b` preserves, item 1 still forces `a` to fix the point `t^-1 y` of `X`, but
  that point may lie outside `Y`.
- **Projective 2-adic model.** `a: x ↦ x + 1` fixes only `∞` on
  `Q_2 ∪ {∞}`, and `b: x ↦ 2x` fixes `0` and `∞`. In `BG`, `b = t a t^-1`, so
  `Fix(b) = t Fix(a)` has as many points as `Fix(a)`, which is false here.
  Hence no extension exists. ∎

**Scope.** For `BG_n = < a, t | b a b^-1 = a^n >` with `n ≥ 3`, the same steps
give `b(x) = c + nx`. A fixed point then needs `(n-1)x = -c` to be solvable in
`K`, which can fail, e.g. on `Z_3` with `n = 4`. So only `n = 2` is claimed.
