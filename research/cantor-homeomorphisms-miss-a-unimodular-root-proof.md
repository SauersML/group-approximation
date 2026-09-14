---
rg: 2
id: cantor-homeomorphisms-miss-a-unimodular-root-proof
kind: route
title: The adjunction group is dihedral of order 18, and none of its transitive actions has S_3-orbits of sizes one and three only
target: cantor-homeomorphisms-miss-a-unimodular-root
requires: []
---

Elementary. We prove item 2; item 1 is its special case `Omega = C`.

## Step 1: the adjunction group is `D_9`

Let `G_w = <a, b, x | a^2, b^2, (ab)^3, x a x a x^(-1) b>`. The first three
relators present `S_3`.
- **Eliminate `b`.** The last relator gives `b = x a x^(-1) a x^(-1)`, using
  `a = a^(-1)`.
- **`b^2`.** Then `b^2 = x a x^(-2) a x^(-1)`, because the middle `x^(-1) x`
  cancels and `a^2 = 1`. So `b^2 = 1` holds iff `a x^(-2) a = 1`, iff `x^2 = 1`.
- **`(ab)^3`.** With `x^2 = 1` we get `b = x a x a x`, so `ab = (ax)^3` and
  `(ab)^3 = (ax)^9`.

Hence `G_w = <a, x | a^2, x^2, (ax)^9>`, the dihedral group of order `18`.
Write `r = ax`, of order `9`, and `s = a`. Then `x = s r`, `b = s r^3`, and
the coefficient subgroup is `S_3 = <s, r^3>`, of order `6`.

## Step 2: a root gives a `G_w`-set

Suppose `x in Sym(Omega)` solves the equation for the given `a, b`. Then
`a^2 = 1`, and `x a x^(-1) a x^(-1) = b` satisfies `b^2 = 1` and
`(ab)^3 = 1`. So `a -> a`, `x -> x` defines a homomorphism
`G_w -> Sym(Omega)`, and `Omega` is a `G_w`-set.

Its restriction to the coefficient `S_3 = <a, b>` is the given action. Every
`G_w`-orbit is finite, hence `G_w/K` for some subgroup `K`. A point `gK` has
`S_3`-orbit of size `[S_3 : S_3 ∩ gKg^(-1)]`.

## Step 3: no transitive `G_w`-set qualifies

We need a `K` such that `S_3 ∩ gKg^(-1)` has order `6` or `2` for every `g`,
and order `2` for some `g`. The subgroups of `D_9` are the rotation subgroups
`<r^d>` with `d | 9`, and the dihedral subgroups `<r^d, s r^k>`. In `D_9` all
nine reflections `s r^j` are conjugate, since `9` is odd, and `S_3` contains
exactly `s, s r^3, s r^6`.

| `K` | `S_3 ∩ gKg^(-1)` | orbit size | qualifies? |
|---|---|---|---|
| rotations `<r^d>` | rotations, order `1` or `3` | `6` or `2` | no |
| order `2`, `<s r^k>` | trivial whenever `gKg^(-1) = <s r^j>` with `3 ∤ j` | `6` | no |
| order `6`, `<r^3, s r^k>` | `<r^3>` whenever `gKg^(-1) = <r^3, s r^j>` with `3 ∤ j` | `2` | no |
| `K = D_9` | all of `S_3` (one point) | `1` | no size-`3` orbit |

So every transitive `G_w`-set whose `S_3`-orbits all have size `1` or `3` is a
single point, where `S_3` acts trivially.

## Step 4: conclusion

The hypothesis gives `Omega` a point in an `S_3`-orbit of size `3`. Its
`G_w`-orbit is a transitive `G_w`-set, every one of its `S_3`-orbits has size
`1` or `3`, and it is not a single point. Step 3 rules this out. So no root
exists.

**Consistency check.**
- **The overgroup root exists.** `G_w` acting on itself by left
  multiplication is a transitive 18-point `G_w`-set. There `S_3` acts freely,
  so its orbits have size `6`, and `x` is a genuine root.
- **Sym(Omega) census.** The obstruction lies only in the orbit type. This
  matches the census recorded on `infinite-symmetric-groups-miss-a-unimodular-root`:
  no root in `S_K` for `r` natural copies of `S_3`, for `(r, K) = (1, 3..7)`,
  `(2, 6..8)` and `(3, 9)`.
