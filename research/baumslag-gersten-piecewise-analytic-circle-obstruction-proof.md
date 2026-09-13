---
rg: 2
id: baumslag-gersten-piecewise-analytic-circle-obstruction-proof
kind: route
title: The conjugator b of a is conjugate to its own square, so it is tangent to the identity at its fixed points; but a power of b fixes a gap end of a with derivative different from 1
target: baumslag-gersten-embeds-in-no-piecewise-analytic-circle-group
requires:
  - piecewise-analytic-circle-square-conjugate-has-parabolic-ends
---

Write "the lemma" for `piecewise-analytic-circle-square-conjugate-has-parabolic-ends`.

**Item 1 (orientation).**
- Let `ε : PA(S^1) → Z/2` be the orientation character.
- `ε(a) = ε(b a b^-1) = ε(a^2) = ε(a)^2 = 1`.
- Put `c = t b t^-1`. Then `b` and `c` are conjugates of `a`, so `ε(b) = ε(c) = 1`.
- So `A = ρ(a)`, `B = ρ(b)` and `C = ρ(c)` lie in `PA_+(S^1)`.

**Item 2 (two square relations).**
- `B A B^-1 = A^2` is the relator.
- Conjugating it by `t` gives `t b t^-1 · t a t^-1 · t b^-1 t^-1 = t a^2 t^-1`,
  that is `c b c^-1 = b^2`. So `C B C^-1 = B^2`.

**Item 3 (contradiction).** Suppose `A ≠ 1`.
- **A power of `B` is hyperbolic at a gap end of `A`.** By the lemma with `n = 2`,
  `A` has a fixed point. Take a gap `J` of `A` with endpoint `p`. Lemma Items 1
  and 3, for `(g,h) = (A,B)`, give `N ≥ 1` with `B^N(p) = p`, and the one-sided
  derivative of `B^N` at `p` from `J` is `2^(-N/m) ≠ 1`.
- **`B` fixes `p` and is tangent to the identity there.**
  - By the lemma for `(g,h) = (B,C)` with `n = 2`, `B` has a fixed point.
  - Every periodic point of an orientation-preserving circle homeomorphism with
    a fixed point is fixed, so `B(p) = p`.
  - Lemma Item 2 for `(B,C)` says both one-sided derivatives of `B` at `p` are `1`.
- **The contradiction.** `B` fixes `p` and preserves orientation, so it maps the
  `J` side of `p` to itself. The chain rule for one-sided derivatives at a fixed
  point gives `(B^N)'(p) = B'(p)^N = 1` from that side, which contradicts the
  first step.

Hence `A = 1`.

**Item 4 (image).** `ρ` factors through `BG / <<a>>`. Adding `a` to the
presentation kills the relator, so the quotient is `< t > ≅ Z`.
