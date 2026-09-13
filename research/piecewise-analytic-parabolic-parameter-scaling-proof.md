---
rg: 2
id: piecewise-analytic-parabolic-parameter-scaling-proof
kind: route
title: Fixed sets of piecewise-analytic maps have finitely many components, so a power of the conjugator fixes the gap ends; there the derivative of g is forced to be 1, and the leading parabolic coefficient scales by the conjugator's derivative
target: piecewise-analytic-circle-square-conjugate-has-parabolic-ends
requires: []
---

Notation is as in the target. Standard facts about the rotation number `rot` of
`f ∈ Homeo_+(S^1)`: `rot(k f k^-1) = rot(f)`, `rot(f^j) = j rot(f)` mod `1`,
`rot(f) = 0` exactly when `f` has a fixed point, and then every periodic point of
`f` is fixed.

**Item 0 (`n = 2`).** `rot(g) = rot(h g h^-1) = rot(g^2) = 2 rot(g)` mod `1`, so
`rot(g) = 0` and `g` has a fixed point.

**Item 1 (components).**
- Let `I` be the closure of a component of `S^1 \ B_g`, and let `G` be an analytic
  lift of `g` on a neighbourhood of `I`. `G(x) - x` is analytic and bounded on
  `I`, so it takes only finitely many integer values there. For each integer `k`,
  the set `{G(x) - x = k}` is either all of `I` or finite. So `Fix(g) ∩ I` is `I`
  or finite, and `Fix(g)` is a finite union of closed arcs and points.
- `h Fix(g) = Fix(h g h^-1) = Fix(g^n)`. `g` has a fixed point, so its periodic
  points are fixed, and `Fix(g^n) = Fix(g)`.
- So `h` permutes the finitely many components of `Fix(g)`. Choose `N ≥ 1` with
  `h^N` preserving each of them. `h^N` also permutes the gaps and preserves the
  cyclic order. The gap leaving a component `K` in the positive direction is
  determined by `K`, so `h^N` maps every gap `J` onto itself. An
  orientation-preserving homeomorphism mapping an open arc onto itself fixes both
  of its endpoints.
- Induction gives `h^j g h^-j = g^(n^j)`, in particular
  `h^N g h^-N = g^(n^N)`.

**Item 2 (derivative at a gap end).**
- Let `p` be an endpoint of a gap `J`. Take an analytic chart `φ : (-ε, ε) → S^1`
  with `φ(0) = p` and `φ((0,ε)) ⊂ J`.
- On `[0, δ)`, `φ^-1 g φ` agrees with the analytic diffeomorphism `ĝ` of a
  neighbourhood of `0` given by the piece of `g` on the `J` side of `p`. The same
  holds for `h^N`, giving `ĥ`: `h^N` fixes `p` and maps `J` onto itself. Both
  maps are increasing with `ĝ(0) = ĥ(0) = 0`.
- Points of `J` are not fixed, so `ĝ` is not the identity on any `(0, δ')`.
- By Item 1, `ĥ ĝ ĥ^-1` and `ĝ^(n^N)` agree on some `[0, δ'')`. Both are analytic
  near `0`, so by the identity theorem they have the same Taylor series at `0`.
- With `λ = ĝ'(0) > 0`, first-order coefficients give `λ = λ^(n^N)`. Since
  `n^N ≥ 2`, `λ = 1`.

**Item 3 (parabolic parameter).**
- **Expansion of `g`.** `ĝ` is analytic with `ĝ'(0) = 1` and is not the identity,
  so `ĝ(x) = x + c x^(m+1) + O(x^(m+2))` with `m ≥ 1` and `c ≠ 0`.
- **Powers.** By induction, `ĝ^k(x) = x + k c x^(m+1) + O(x^(m+2))` for `k ≥ 1`:
  `ĝ(ĝ^(k-1)(x)) = ĝ^(k-1)(x) + c (ĝ^(k-1)(x))^(m+1) + O(x^(m+2))`, and
  `ĝ^(k-1)(x) = x + O(x^2)`.
- **Conjugation.** Write `ĥ(y) = ν y + O(y^2)` with `ν > 0`, so
  `ĥ^-1(x) = x/ν + O(x^2)`. Put `y = ĥ^-1(x)`. Then `ĝ(y) = y + c y^(m+1) + O(y^(m+2))`
  and `ĥ'(y) = ν + O(y)`. So
  `ĥ(ĝ(y)) = ĥ(y) + ĥ'(y) c y^(m+1) + O(y^(m+2)) = x + ν c (x/ν)^(m+1) + O(x^(m+2))`,
  that is, `ĥ ĝ ĥ^-1(x) = x + c ν^(-m) x^(m+1) + O(x^(m+2))`.
- **Comparison.** Item 2 equates this with `ĝ^(n^N)`, so `c ν^(-m) = n^N c`.
  Since `c ≠ 0`, `ν^m = n^(-N)` and `ν = n^(-N/m) ≠ 1`. This is target Item 3.

**Item 4 (all fixed points).** Let `p ∈ Fix(g)` and fix a side of `p`.
- If `g` is the identity on a one-sided neighbourhood of `p` on that side, the
  one-sided derivative is `1`.
- Otherwise non-fixed points accumulate at `p` from that side. `Fix(g)` has
  finitely many components, so a one-sided neighbourhood `(p, p+ε)` (or
  `(p-ε, p)`) contains no fixed point. It lies in a gap with endpoint `p`, and
  Item 2 gives derivative `1`.

This is target Item 2. Item 1 is target Item 1.
