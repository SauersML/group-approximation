---
rg: 2
id: l1-product-word-metrics-admit-no-contracting-combing-proof
kind: route
title: Arrival times must grow by C/2 on each side of a square of C-moves in alternating factors
target: l1-product-word-metrics-admit-no-contracting-combing
requires: []
artifacts:
  - research/artifacts/zaremsky-4-01-contracting-combings-2026-09-16.md
---

Complete proof: artifact Sections 4 and 5 (Lemma 4, Theorem 5, Corollary 5′).
Condensed here.

**Notation.**
- `s` is a combing that is contracting with constant `C`, and `c = ⌊C/2⌋ >= 1`.
- The arrival time is `T(x) = min{t : s(x)(u) = x for all u >= t}`, so `T(x) >= 1` for
  `x ≠ 1`.
- For `x ≠ 1`, `p'(x) = s(x)(T(x) − 1)`, the last point before arrival. It satisfies
  `d(p'(x), x) = 1`.

**Arrival rule.** If `x ≠ 1`, `d(x, q) <= C` and `d(p'(x), q) > C`, then
`T(q) >= T(x) + c`.

*Proof.* Otherwise `n := T(x) + c − 1 >= T(q)`. Take `n' = n`, so `n' <= n` and
`c <= n`. Then `s(x)(n) = x` and `s(q)(n') = q`, which are at distance `<= C`. The
contracting condition gives `d(s(x)(n − c), q) <= C`. But `s(x)(n − c) = p'(x)`. ∎

**Theorem.** In `G × H` with metric `d_G + d_H`, a point `p'(x)` adjacent to `x`
differs from `x` in exactly one factor. Call that factor `α(x)`. A *`β`-move of `x` by
`C`* is a point that agrees with `x` in the other factor and whose `β`-coordinate is
at `d_β`-distance exactly `C` from that of `x`.

- *Claim 1.* If `x ≠ 1`, `β ≠ α(x)` and `q` is a `β`-move of `x` by `C`, then
  `T(q) >= T(x) + c`.

  *Proof.* `d(x, q) = C` and `d(p'(x), q) = 1 + C`. Apply the arrival rule. ∎
- *Claim 2.* If moreover `q ≠ 1`, then `α(q) = β`.

  *Proof.* Otherwise `α(q) = α(x) ≠ β`. Since `x` is a `β`-move of `q`, Claim 1 at
  `q` gives `T(x) >= T(q) + c >= T(x) + 2c`. ∎

Since `G` and `H` are infinite, their spheres of every radius are nonempty.
- Pick `g` with `|g| > C` and `g'` with `d_G(g, g') = C`.
- Pick `h` with `|h| > C` and `h'` with `d_H(h, h') = C`.

Then `g, g', h, h' ≠ 1`, so the four corners `(g,h)`, `(g,h')`, `(g',h')`, `(g',h)` are
nontrivial. By symmetry assume `α(g, h) = G`. Go round the square:
- `(g, h) → (g, h')` is an `H`-move, so `T` increases by at least `c` and the new
  last-step factor is `α = H`.
- `(g, h') → (g', h')` is a `G`-move, so `T` increases by at least `c` and `α = G`.
- `(g', h') → (g', h)` is an `H`-move, so `T` increases by at least `c` and `α = H`.
- `(g', h) → (g, h)` is a `G`-move, so `T` increases by at least `c`.

Each move is in the factor other than the current `α`, so Claim 1 applies at every
step, and Claim 2 supplies the next `α`. So `T(g, h) >= T(g, h) + 4c`, a
contradiction. ∎

**Consequences.**
- `Z^d = Z × Z^{d−1}`, where the standard generators are the disjoint union of the
  factors' standard generators.
- `A_{Γ_1 * Γ_2} = A_{Γ_1} × A_{Γ_2}`, where the standard generators split the same
  way, and RAAGs on nonempty graphs are infinite.
- `Z^2` with `{−1,0,1}^2 ∖ {0}` is covered by
  `linf-lattice-groups-admit-contracting-combings`.

**Numerical check.** Evidence only:
`experiments/zaremsky-4-01-contracting-combings-2026-09-16/check_combings.py`,
Part 5. It runs the square construction as a certificate generator against four
concrete combings of `Z^2` with the standard generators and re-verifies each
violation directly, for `C = 2..7`.
