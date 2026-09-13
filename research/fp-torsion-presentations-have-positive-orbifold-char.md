---
rg: 2
id: fp-torsion-presentations-have-positive-orbifold-char
kind: claim
title: A finite presentation of a torsion group has positive orbifold characteristic at every finite quotient
---

**Setting.** Let `G = <X | R>` with `X` and `R` finite and no relator trivial
in the free group `F(X)`. Each `r in R` is uniquely `r = u_r^(n_r)` in
`F(X)`, with `n_r >= 1` and `u_r` not a proper power. For a surjection
`q: G -> Q` onto a finite group, let `o_Q(r)` be the order of `q(u_r)`; it
divides `n_r`. Put

```text
chi_Q(X,R) = 1 - |X| + sum_(r in R) 1/o_Q(r).
```

**Theorem.** If `G` is a torsion group, then `chi_Q(X,R) >= 1/|Q|` for every
finite quotient `Q` of `G`. If `G` is moreover residually finite, then
`chi_G(X,R) = 1 - |X| + sum_r 1/o_G(r) > 0`, where `o_G(r)` is the order of
`u_r` in `G`.

**Consequences for Zaremsky Problem 1.11.**
- With `Q = 1`: `|R| >= |X|`. Every finite presentation of a torsion group
  has deficiency at most `0`.
- A single finite quotient can rule out torsion. If some finite quotient `Q`
  has `chi_Q(X,R) < 1/|Q|`, then `G` is not torsion. No residual finiteness is
  needed for this.
- Suppose every relator is an honest power: `u_r` has order exactly `n_r` in
  `G`. If also `1 - |X| + sum_r 1/n_r <= 0`, then `G` is not a residually
  finite torsion group. In particular, take relators `u_r^(p^(k_r))` with
  `u_r` of order exactly `p^(k_r)`. Then `chi_G = -def_p(X,R)`, for the
  `p`-deficiency described in
  `research/artifacts/fpbs/docs/power-p-deficiency-excludes-t-2026-09-11.md`,
  and nonnegative `p`-deficiency with honest orders rules out residually
  finite torsion. Infinitely presented torsion groups of positive
  `p`-deficiency exist, as recorded in that artifact, so this is a genuine
  fence for finite presentations.

**Model tests.**
- `A_5 = <a, b | a^2, b^3, (ab)^5>`: `chi = 1 - 2 + 1/2 + 1/3 + 1/5 = 1/30`,
  and `1/30 >= 1/60 = 1/|A_5|`, as the theorem requires.
- `<a, b | a^2, b^3, (ab)^7>`: `chi = -1/42 < 0`. The group is infinite and
  residually finite, so the theorem says it is not torsion. Indeed it contains
  elements of infinite order.
- `Z/2 * Z/2 = <a, b | a^2, b^2>` with `Q = Z/2 x Z/2`: `chi_Q = 0 < 1/4`, so
  the group is not torsion. Here `ab` has infinite order.
- `Z^2 = <a, b | [a, b]>`: `[a, b]` is not a proper power and `o_G = 1`, so
  `chi_G = 0`, and `Z^2` is not torsion.
- For triangle presentations `chi` is the orbifold Euler characteristic of the
  sphere with three cone points. Positivity is exactly the spherical case,
  which is the case of finite groups.

**Credit.** This is the Reidemeister–Schreier relator count used for
rational Euler characteristics of groups with torsion and for `p`-deficiency.
No novelty is claimed. Its use here is as an obstruction for Problem 1.11.

Proof: `fp-torsion-presentations-have-positive-orbifold-char-proof`.
