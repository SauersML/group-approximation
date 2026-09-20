---
rg: 2
id: lifted-thompson-t-shift-template-dies-proof
kind: route
title: Apply word-level commuting-conjugate localization with epsilon empty, read d(sI) off the short cofactor, and feed the kill criterion of the stabilizer-function node
target: lifted-thompson-t-shift-template-dies-for-all-words
requires:
  - commuting-conjugate-commutator-area-localizes-conjugators
  - lifted-thompson-t-mf-radical-dichotomy
---

This is a complete direct proof.  It uses:

- `commuting-conjugate-commutator-area-localizes-conjugators` (special case);
- items 1 and 3 of `lifted-thompson-t-shift-template-area-is-a-stabilizer-function`
  and its proof (commit `e56d5901da`).  These give the exact per-arc identity
  and the interval invariant.  Both are restated below where they are used.

## Hypotheses of the lemma

`T̄` is torsion-free.  It is a subgroup of `Homeo^+(R)` (the lifts commuting
with `x -> x+1`; see `lifted-thompson-t-mf-radical-dichotomy`), and
`Homeo^+(R)` is torsion-free: if `g(p) > p`, then `g^n(p) > p` for all
`n >= 1`.  `c` and `c_K` are
nontrivial with disjoint supports `int(I) + Z` and `int(K) + Z`.  So they
commute, and `c^p c_K^q = 1` forces `p = q = 0`.  Hence `H = <c, c_K> ≅ Z^2`,
with basis `c, c_K`.  For `d in D` and any word `δ` for `d`, the element of
`δ c δ^(-1)` is `c`, which commutes with the element `c_K` of `kappa`.

## Item 1

Let `f(d) <= A`, attained by a word `δ`.  The special case of the lemma, with
the rank-two constant (`H ≅ Z^2` with basis `c, kappa`), gives `d = h_0 g` with
`h_0 in H`, `g in D` and `|g| <= R(A)`.

Now compute `d(sI)`.  Here `sI = [1/16, 1/8] ⊂ [0, 5/16)` (mod `Z`), which is
disjoint from `I` and `K`.  So `sI ⊂ Fix(c) ∩ Fix(c_K)`.  Since `g` commutes with
`c` and with `c_K`, it maps `Fix(c)` onto `Fix(c)` and `Fix(c_K)` onto
`Fix(c_K)`, so `g(sI) ⊂ Fix(c) ∩ Fix(c_K)`.  Every element of `H` fixes that set
pointwise.  Therefore

```text
d(sI) = h_0(g(sI)) = g(sI),     g in B_(R(A)),
```

which takes at most `|B_(R(A))|` values.

## Item 2

Let `E ⊂ D` be infinite, with the intervals `d(sI)` (`d in E`) pairwise
distinct.  If `f <= A` on `E`, item 1 bounds `|E|` by `|B_(R(A))|`, which is a
contradiction.  So `f` is unbounded on `E`.  This is (P).

## Item 3

The following facts are items 1 and 3 of the stabilizer-function node.

- For the arc `a -> b = (j,l,m)`, the word `δ_ab = σ^(-1) u_a^(-1) u_b`
  represents `d_ab in D`.
- Freely and up to conjugation, `[C_b, H_a]` equals
  `[δ_ab c δ_ab^(-1), kappa]`, so
  `Area([C_b, H_a]) = Area([δ_ab c δ_ab^(-1), kappa]) >= f(d_ab)`.
- For fixed `a`, the intervals `d_ab(sI) = s^(-1) t_a^(-1)(alpha_m)`, `m > l`,
  are pairwise distinct.

By item 1, at most `|B_(R(A))|` of these arcs have `f(d_ab) <= A`, and so at
most that many have `Area([C_b, H_a]) <= A`.  This holds for every choice of
the words `u_v` and of the free parts of the `t_v`, because item 1 holds for
every word `δ`.  Since each vertex has infinitely many out-arcs, the supremum
of the cross-commutator area over the out-star of `a` is infinite.  This is
item 4 of the stabilizer-function node (its kill criterion), now
unconditional.

## Independence of the wave-20 obstructions

- *Length alone cannot work.*  The proof never bounds `|δ|`.  It bounds the
  number of `H`-orbits of edges that `P_δ` meets.  Under `δ -> kappa^p δ c^q`
  that number changes by at most `|kappa| + |c|`, independently of `p, q`.
  This holds because `P_(kappa^p)` and `P_(c^q)` are sums of `H`-translates of
  `P_kappa` and `P_c`, and left translation by `H` preserves `H`-orbits.  This
  agrees with item 2 of the stabilizer-function node.
- *Linear certificates with non-faithful coefficients are constant*
  (`thompson-template-area-sees-only-faithful-coefficients`, wave 22).  The
  certificate here is the `l^1` norm on the regular permutation module
  `C_1(Cay(T̄))`, which is faithful.
