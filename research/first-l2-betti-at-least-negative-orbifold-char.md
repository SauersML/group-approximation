---
rg: 2
id: first-l2-betti-at-least-negative-orbifold-char
kind: claim
title: For an infinite finitely presented group the first L2-Betti number is at least minus the orbifold characteristic of the presentation
distinct_from:
  fp-torsion-presentations-have-positive-orbifold-char: that counts relators in finite quotients and needs torsion; this counts von Neumann dimensions in the group itself, needs no finite quotients, and holds for every infinite group
  ghb7-l2-betti-two-is-orbifold-euler-characteristic: that computes a second L2-Betti number of one hyperbolic group through its orbifold Euler characteristic; this is a lower bound for the first L2-Betti number of any infinite finitely presented group
---

**Setting.** Let `G = <X | R>` be infinite, with `X` and `R` finite and no
relator trivial in `F(X)`. Write `r = u_r^(n_r)` with `u_r` not a proper
power, and let `o_G(r)` be the order of `u_r` in `G`. It divides `n_r`,
because `u_r^(n_r) = r = 1` in `G`. Put
`chi_G(X,R) = 1 - |X| + sum_(r in R) 1/o_G(r)`.

**Theorem.**

```text
b_1^(2)(G) >= -chi_G(X,R) = |X| - 1 - sum_r 1/o_G(r).
```

**Corollary.** If `G` is infinite and amenable, then `chi_G(X,R) >= 0` for
every finite presentation of `G`.

**Consequences for Zaremsky Problem 1.11.**
- An amenable finitely presented infinite torsion group needs
  `sum_r 1/o_G(u_r) >= |X| - 1`. Amenable torsion candidates, such as groups
  in the Grigorchuk circle, must meet this.
- A finitely presented infinite torsion group with `chi_G(X,R) < 0` has positive
  first L2-Betti number. So it is non-amenable and has no infinite normal
  amenable subgroup. By `fp-torsion-presentations-have-positive-orbifold-char`
  it is also not residually finite.

**Model tests.**
- `Z^2 = <a, b | [a, b]>`: `o = 1`, `chi = 0`, `b_1^(2) = 0`.
- `D_infinity = <a, b | a^2, b^2>`: `chi = 1 - 2 + 1/2 + 1/2 = 0`, amenable,
  `b_1^(2) = 0`.
- The `(2,3,7)` triangle group: `chi = -1/42`, and its first L2-Betti number
  is `1/42`, so the bound is sharp there.
- `F_2 = <a, b | >`: `chi = -1`, `b_1^(2) = 1`.

**Credit.** The dimension count is standard for groups given by power
relators. No novelty is claimed. The amenable corollary uses Cheeger–Gromov
vanishing through `l2-betti-numbers-vanish-with-infinite-normal-amenable-subgroup`.

Proof: `first-l2-betti-at-least-negative-orbifold-char-proof`.
