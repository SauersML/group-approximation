---
rg: 2
id: kl-length-six-one-coincidence-words-inject
kind: claim
title: Length-six words with exactly one same-sign coincidence inject when the light same-sign cycle has infinite order and misses the coincidence coset
distinct_from:
  kl-four-same-sign-corner-words-inject: that needs at least four light same-sign corners, so at length six it excludes every coincidence; this treats the next case, one trivial same-sign 2-cycle and two light same-sign corners, under an infinite-order hypothesis on the light cycle.
  kl-unit-exponent-words-inject-when-same-sign-corners-are-free: that needs the same-sign labels to generate a free group, which fails as soon as one 2-cycle is trivial; this allows exactly one trivial 2-cycle.
  kl-length-six-four-sign-change-words-inject: that settles the two length-six classes with two same-sign corners; this concerns the two classes with four same-sign corners and one coincidence among them.
---

Let `G` be any group, and let `w in G * <t>` be cyclically reduced, not a
proper power, of `t`-length six. Suppose its sign class is `+++++-` or
`++++--` after splitting powers of `t` into single letters, so that a corner
inside a power carries the label `1`.

Use the star-graph convention of `kl-four-same-sign-corner-words-inject`:
- a corner `t g t` is a P-edge `t^- -> t^+` with label `g`;
- a corner `t^(-1) h t^(-1)` is an N-edge `t^+ -> t^-` with label `h`.

Let `y` be the loop coefficient at `t^-` (the corner `t y t^(-1)`), and `x`
the loop coefficient at `t^+` (the corner `t^(-1) x t`). The four same-sign
corners carry labels in one of three patterns.

| Pattern | Class | Same-sign labels | `lambda` | `lambda'` | `kappa` |
|---|---|---|---|---|---|
| (F1) | `++++--` | P-labels `u, g, h`; N-label `u^(-1)` | `g h^(-1)` | `h^(-1) g` | `u h^(-1)` |
| (F2) | `++++--` | P-labels `u, u, g`; N-label `n` | `g n` | `n g` | `u n` |
| (F3) | `+++++-` | P-labels `u, u, g, h` | `g h^(-1)` | `h^(-1) g` | `u h^(-1)` |

Assume:
1. `lambda` has infinite order;
2. `kappa` is not in `<lambda>`;
3. `y` is not in `<lambda>`, and `x` is not in `<lambda'>`.

Then `G -> (G * <t>)/<<w>>` is injective, and every reduced spherical picture
over `<G, t | w>` is empty.

**Torsion loops.** If `x` and `y` have finite order, for example if they are
involutions, then condition 3 follows from condition 1. Every nontrivial
element of the infinite cyclic groups `<lambda>` and `<lambda'>` has infinite
order. Nothing else is assumed about torsion.

**Exactly one coincidence.** Conditions 1 and 2 rule out a second coincidence.
- In (F1) and (F3), `g = h` gives `lambda = 1`, and `g = u` gives `kappa = lambda`.
- In (F2), `g n = 1` gives `lambda = 1`, and `g = u` gives `kappa = lambda`.

So the four same-sign corners close exactly one trivial 2-cycle: two heavy
corners and `r = 2` light ones, in the terms of the four-corner theorem.

## Consequences

**Length six over any group.** Combine this with two other results:
- `kl-four-same-sign-corner-words-inject` handles `r >= 4`. With four same-sign
  corners, `r = 3` cannot occur, because heavy corners come in pairs.
- `kl-length-six-four-sign-change-words-inject` handles the classes with two
  same-sign corners.

A length-six Kervaire--Laudenbach violation over any group therefore needs one
of the following:
- **Two or more same-sign coincidences** (`r <= 1`). The weight test with
  weight one on both loops is then impossible, because the heavy corners and
  loops already exceed the budget `n - 2 = 4`.
- **Exactly one coincidence, with an exception:** `lambda` has finite order, or
  `kappa in <lambda>`, or an infinite-order loop coefficient lies in `<lambda>`
  or `<lambda'>`.
- **Four sign changes,** with the finite-order or absorption exceptions of that
  theorem.

**Torsion loops.** In the Leavitt search both sign-change coefficients are
involutions. So only the `r <= 1` case and the first two exceptions (finite-order
`lambda`, `kappa in <lambda>`) remain.

**The Leavitt three-gate word.** The word `(L6G.1)` of
`leavitt-length-six-three-gate-weight-survivor` is pattern (F1) with `u = 1`,
`g = q`, `h = p`. If `q p^(-1)` has infinite order in
`EL_20(L_(F_2)(1,2))`, this theorem fences it directly: `kappa = p^(-1)` cannot
lie in `<lambda>`, because `p` has order 20. The word is already fenced by the
Nielsen amalgam of `leavitt-three-gate-candidate-is-injective`.

## Provenance and novelty

- **Method.** The weight conditions and the curvature derivation are those of
  `kl-four-same-sign-corner-words-weight-proof`. That route follows the
  Bogley--Pride weight test through the Ahmad--Al-Mulla--Edjvet restatement,
  not read at source, and derives injectivity directly.
- **Literature checked.** Edjvet--Juhász, *Non-singular equations over groups
  I*, Algebra Colloq. 18 (2011), treats pairwise distinct exponent magnitudes
  and coefficients of order greater than two, according to its abstract. Unit
  exponents with coincident labels and involution loops fall outside that
  statement.
- **Not checked.** Part II of Edjvet--Juhász was not read, so novelty is
  unverified.

DERIVATION
kl-length-six-one-coincidence-weight-proof
