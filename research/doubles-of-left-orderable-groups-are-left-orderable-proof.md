---
rg: 2
id: doubles-of-left-orderable-groups-are-left-orderable-proof
kind: route
title: The fold kernel acts freely on the Bass--Serre tree, so the double is free-by-orderable
target: doubles-of-left-orderable-groups-are-left-orderable
requires: []
artifacts:
  - research/artifacts/bengi-wise-doubles-left-orderable-2026-09-16.md
---

Full details are in §2 of the artifact (Lemmas 2.1--2.4).

Bass--Serre theory is used in the form of Serre, *Trees* (Springer, 1980),
Chapter I, as in `double-ascending-hnn-atiyah-kernel-tree-proof`. Two facts
are used, and the section numbers were not re-checked on 2026-09-16:
- an amalgam `A *_C B` acts without inversion on a tree whose vertex
  stabilizers are the conjugates of `A` and `B`;
- a group acting freely without inversion on a tree is free.

A left order is encoded by a positive cone `Pi`, with `Pi Pi ⊆ Pi` and
`G = Pi ⊔ Pi^-1 ⊔ {1}`. Subgroups of left-orderable groups are
left-orderable.

**Step 1 (extensions).** If `1 -> N -> E -> Q -> 1` is exact with `N` and `Q`
left-orderable, then `E` is left-orderable. Let `pi` be the quotient map, with
positive cones `Pi_N` and `Pi_Q`, and put `Pi = pi^-1(Pi_Q) ∪ Pi_N`.
- *Trichotomy.* If `pi(g) != 1`, exactly one of `pi(g)` and `pi(g)^-1` lies
  in `Pi_Q`. If `g in N \ {1}`, exactly one of `g` and `g^-1` lies in `Pi_N`.
- *Closure.*
  - If `g` and `h` both lie in `pi^-1(Pi_Q)`, then `gh` does.
  - If exactly one lies there and the other lies in `N`, then `pi(gh)` is the
    image of the first, so `gh` lies there.
  - If both lie in `Pi_N`, then `gh` does.

**Step 2 (free groups).** Every free group `F(S)` is left-orderable.
- Let `U` be the group `1 + m` inside the ring of noncommutative power series
  in `X_s` whose homogeneous components are finite sums. Here `m` is the ideal
  of series with zero constant term, and `(1+h)^-1 = sum (-h)^n`.
- The Magnus map `s -> 1 + X_s` is injective. For a reduced word
  `s_1^{e_1} ... s_r^{e_r}` with `r >= 1`, the monomial `X_{s_1} ... X_{s_r}`
  has no square subword, so it can only come from the linear terms `e_i X_{s_i}`
  of the factors. Its coefficient is `e_1 ... e_r != 0`.
- Order the monomials of each degree lexicographically. For `u = 1 + h != 1`,
  let `c(u)` be the coefficient of the least monomial in the lowest nonzero
  homogeneous component of `h`. Put `Pi = {u : c(u) > 0}`.
  - *Trichotomy.* `u^-1 - 1 = -h + h^2 - ...` has the same lowest component as
    `-h`, so `c(u^-1) = -c(u)`.
  - *Closure.* `uv - 1 = h + k + hk`, and `hk` starts in a strictly higher
    degree. If the lowest degrees of `h` and `k` differ, the lower component
    survives. If they agree, the least monomial occurring in either component
    has a coefficient that is a sum of two nonnegative numbers, at least one of
    them positive.

**Step 3 (the general amalgam).** Let `phi : E = A *_C B -> L` be a
homomorphism to a left-ordered group `L` that is injective on `A` and on `B`.
Put `N = ker phi`.
- Since `N` is normal, `N ∩ gAg^-1 = g(N ∩ A)g^-1 = 1` for every `g in E`, and
  likewise for `B`.
- `N` acts without inversion on the Bass--Serre tree of `E`, and its vertex
  stabilizers are `N ∩ gAg^-1` and `N ∩ gBg^-1`, all trivial. So `N` acts
  freely, and `N` is free.
- By Step 2, `N` is left-orderable. `E/N ≅ phi(E) <= L` is left-orderable.
- By Step 1, `E` is left-orderable.

**Step 4 (the double).** The fold `rho : D -> A` sends `a -> a` and
`\underline a -> a`. The two maps agree on `C = \underline C`, so `rho` is
well defined. It restricts to the identity on `A` and to the inverse copy map
on `\underline A`, so it is injective on both factors. Step 3 with `L = A`
shows that `D` is left-orderable.

**Step 5 (consequences).**
- In a left-ordered group, `g > 1` gives `1 < g < g^2 < ...`, so no
  nontrivial power is `1`.
- For finite nonempty `X, Y`, the maximum `m` of `XY` has a unique
  expression. If `m = xy`, then `y = max Y`: for `y < max Y` we would get
  `xy < x max Y <= m`. So `x = m (max Y)^-1`.
- Hence, for nonzero `alpha, beta in k[D]`, the coefficient of `max(supp alpha
  supp beta)` in `alpha beta` is a product of two nonzero coefficients, and
  `k[D]` is a domain.

Iterating Step 4 from Step 2 gives the statement for iterated doubles of free
groups. A subgroup of a left-orderable group is left-orderable, which gives
the last sentence of the target.
