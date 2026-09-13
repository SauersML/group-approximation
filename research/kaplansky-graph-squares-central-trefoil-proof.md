---
rg: 2
id: kaplansky-graph-squares-central-trefoil-proof
kind: route
title: Classify the 36 relation classes of a 4-cycle by explicit automorphisms of F_2, then read off the central extension
target: kaplansky-graph-squares-force-central-trefoil-generators
requires:
  - small-non-up-left-support-has-no-orderable-quotient
  - zero-divisor-support-subgroup-host-constraints
  - fisher-sanchez-peralta-special-and-3-manifold-domains
---

Write `supp alpha = {1, h_2, h_3}`. By A--T Lemma 2.1 (`supp`), for least
`beta` we may assume `G = H = <h_2, h_3>` and `alpha beta = 0` in `k[H]`.

(1) **Relations of a 4-cycle.** A 4-cycle `g_1 ~ g_2 ~ g_3 ~ g_4 ~ g_1`
carries relations `a_i g_i = b_i g_(i+1)` with `a_i, b_i in supp alpha` and
`a_1 != b_1 != a_2 != ... != b_4 != a_1` (A--T Remark r-K3-K3, using
Thm K3-K3). Multiplying gives `r(T) = (a_1^-1 b_1)(a_2^-1 b_2)(a_3^-1 b_3)(a_4^-1 b_4) = 1`
in `H`. `cycle_relators.py` enumerates all 258 tuples, groups them under
rotation and reversal into 36 classes (A--T's count), and for each relator
finds an automorphism `phi` of `F(h_2, h_3)` with `phi(r)` in one of the
normal forms below. The search uses elementary Nielsen moves and conjugation
moves, and each output is an image of `r` under a composition of
automorphisms. `torus_witness.py` re-verifies such an image by direct
substitution. If `phi(r) = t(h_2, h_3)`, then `p = phi^-1(h_2)` and
`q = phi^-1(h_3)`, evaluated at `(h_2, h_3)`, generate `H` and satisfy
`t(p, q) = 1`. The 36 classes split as follows (`census2345.out`):
- **12 classes.** `t` is primitive, or a proper power of a primitive
  element. Torsion-freeness then makes `H` cyclic, hence abelian and
  torsion-free, so `k[H]` is a domain. Contradiction.
- **15 classes.** `t` is `p q^m p^-1 q^-n` with `|m| = 1` or `|n| = 1`, or
  `p^2 q^(+-2)`. Then `H` is a quotient of `BS(1, j)` or of the Klein bottle
  group. Both are solvable, so `H` is elementary amenable. That contradicts
  item 3 of `zero-divisor-support-subgroup-host-constraints`.
- **9 classes.** `t = q^-3 p^-2` up to symmetry. These are exactly A--T
  Table tab-C4 rows 5, 7, 14, 17, 21, 22, 25, 26, 29 (`check_at_tables.out`
  matches each class to one row and checks A--T's substitution
  `x^2 = y^3` in `F(h_2, h_3)`).

So a 4-cycle forces generators `u, v` of `H` with `u^3 = v^2`. Rename so
that `u = q^-1` and `v = p`.

(2) **The central element.** `z = u^3 = v^2` commutes with `u` and with `v`,
so it is central in `H`. It is nontrivial because `u != 1`, which holds
since `H` is not cyclic by (1). It has infinite order because `H` is
torsion-free.

(3) **Trefoil quotient.** `B = <u, v | u^3 = v^2>` maps onto `H`. Let `N` be
the kernel. `N ∩ <u^3> = 1`, since `z` has infinite order in `H`. `B` is the
fundamental group of the exterior of the trefoil knot, a compact 3-manifold,
so `k[B]` is a domain (`fisher-sanchez-peralta-special-and-3-manifold-domains`).
`k[H]` has zero divisors, so `H` is not isomorphic to `B`, and `N != 1`.

(4) **The quotient `Q`.** `Q = H/<z>` is a quotient of
`B/<u^3> = <u, v | u^3, v^2>`, the modular group. If the image of `u` were
trivial, then `u = z^j = u^(3j)`, so `u^(3j-1) = 1`, and `u = 1` by
torsion-freeness, a contradiction. So `u` has image of order `3`. In the same
way `v = z^j = v^(2j)` forces `v = 1`, so `v` has image of order `2`. If `Q`
were finite, `H` would be torsion-free and virtually infinite cyclic, hence
infinite cyclic, which (1) excludes. So `Q` is infinite.

(5) **Betti numbers.** `|supp alpha| = 3 <= 5`, so `H` has no nontrivial
left-orderable quotient and `H^ab` is finite
(`small-non-up-left-support-has-no-orderable-quotient`), and
`H_1(H; Q) = 0`. The central extension `1 -> <z> -> H -> Q -> 1` gives the
exact sequence

```text
H_2(H; Q) -> H_2(Q; Q) -> H_1(<z>; Q)_H = Q -> H_1(H; Q) = 0.
```

The coinvariants equal `Q` because `z` is central. So `H_2(Q; Q)` maps onto
`Q`, and `dim_Q H_2(Q; Q) >= 1`.

**Trust surface.**
- A--T Lemma 2.1 and Thm K3-K3, read in the arXiv TeX source.
- The standard facts used: torsion-free abelian groups are domains, the
  modular group presentation, torsion-free virtually cyclic groups are
  cyclic, and the five-term exact sequence.
- The census scripts, whose outputs are pinned in the artifact.
