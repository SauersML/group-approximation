---
rg: 2
id: fpbs-cs-set-family-hypothesis-fails-commuting-normal-cross
kind: claim
title: If an infinite normal subgroup has a centralizer with infinite image modulo it, as in every direct product of two infinite groups, the set-family hypothesis of Choi-Seo fails for every family, radius and generating set
distinct_from:
  fpbs-cs-set-family-hypothesis-fails-infinite-centre: that proves the failure on groups with infinite centre through the conjugation-expansion test, which needs the conjugates D_R(E) themselves to be few; this splits each conjugate into a K-commutator times an H-conjugate, so only the two factor sets need to be few, and it decides the centreless products F_2 x F_2, F_2 x D_infinity and F_2 x lamplighter that the conjugation-expansion test left open.
  fpbs-infinite-centralizer-forces-price-one: that shows an infinite normal subgroup with infinite centralizer forces fixed price one, an obstruction to the cost route to p_c < p_u; this is an obstruction to the Choi-Seo supporting-set route to (Gamma1) under a similar hypothesis, and says nothing about cost.
  fpbs-product-every-generating-set: that is the open target p_c < p_u on every Cayley graph of a nonamenable direct product; this proves one proof method cannot reach it and proves nothing about the thresholds.
  fpbs-acylindrically-hyperbolic-critical-l2-gap: that imports Choi-Seo's verification of the set-family hypothesis on acylindrically hyperbolic groups; this proves the hypothesis false on a class that, by the two results together, is disjoint from the acylindrically hyperbolic groups.
artifacts:
  - research/artifacts/fpbs-acylindrical-l2-gap-2026-09-16.md
  - experiments/fpbs-commuting-cross-2026-09-17/check_commuting_cross.py
  - experiments/fpbs-commuting-cross-2026-09-17/output.txt
---

**ESTABLISHED.** Proof route:
`fpbs-cs-set-family-hypothesis-fails-commuting-normal-cross-proof`.

**The hypothesis under test.** This is SF(𝓗,R), the hypothesis of Choi–Seo
arXiv:2508.08932v2 `thm:hutchcroft1plus2`, quoted verbatim in
`fpbs-cs-set-family-hypothesis-fails-infinite-centre` and in the artifact (CS4).
It is the only route in [CS] to (Gamma1),
`limsup_(p -> p_c-) (p_c - p) chi_p < infinity`. `B(R)` is the closed `R`-ball
about `e` in the word metric of `S`.

**Theorem.** Let `G` be finitely generated and `S` a finite generating set.
Suppose `G` has subgroups `K` and `H` such that

* `K` is normal in `G`;
* every element of `H` commutes with every element of `K`;
* `K` is infinite and `H ∩ K` has infinite index in `H`.

Then for every `R > 0` and every family `𝓗`, SF(𝓗,R) fails. The witness is
the **commuting cross**. Take `n > 2 #B(R)`, a set `X ⊆ H` of `n` elements in
distinct cosets of `H ∩ K`, and a set `Y ⊆ K` of `n` elements. Put

```text
A  = X Y  ∪  C_1  ∪  C_2,
C_1 = { x h^-1 x^-1 : x in X, h in B(R) },
C_2 = { y h y^-1 h^-1 : y in Y, h in B(R) }.
```

Every point of the core `X Y` fails the necessary condition, so fewer than
`#A/2` points of `A` meet it.

Equivalently, the hypothesis is that `G` has an infinite normal subgroup `K`
whose centralizer `C_G(K)` has infinite image in `G/K`. Take `H = C_G(K)`.

**The key identity.** For `x ∈ H`, `y ∈ K` and any `h ∈ G`,

```text
(x y) h (x y)^-1  =  [y,h] · (x h x^-1),     [y,h] = y h y^-1 h^-1 ∈ K .
```

So each conjugate of a short element by a core point is a quotient `u v^-1`
with `u ∈ C_2` and `v ∈ C_1`. The two factor sets have at most `n #B(R)`
elements each, while the core has `n^2`. The conjugation-expansion test of
`fpbs-cs-set-family-hypothesis-fails-infinite-centre`(b) instead had to put the
conjugates themselves into `A`. On centreless products there are about
`n^2 #B(R)` of them, so that test is silent there.

**Class covered.** The theorem applies on every finite generating set of each
of the following:

* every direct product `H x K` of two infinite groups (take `K` the second
  factor). This includes the cases left open by the infinite-centre node:
  - `F_2 x F_2`, posed by Choi–Seo;
  - `F_2 x D_infinity`, which the conjugation-expansion test did not decide;
  - `F_2 x (Z/2 wr Z)` and every product with a centreless amenable factor;
  - `T x T'` for Tarski monsters and `B(m,n) x B(m',n')`;
  - products of hyperbolic groups, and reducible right-angled Artin and
    CAT(0) cubical groups that split as products (the reducible case of
    Choi–Seo's CAT(0) cubical question);
* every group with infinite centre `Z` and `[G:Z] = infinity` (take `K = Z`
  and `H = G`), which recovers part (c) of the infinite-centre node in that
  case;
* extensions `(H x K) ⋊ F`, and more generally any overgroup, in which `K`
  stays normal and still commutes with `H`. Examples are central products, and
  `Lambda x K` extended by a finite group acting on `K` alone.

The whole direct-product class of `fpbs-product-every-generating-set` is
covered: with `H`, `K` infinite, `K` is normal, `H ∩ K = {e}`, and `H`
centralizes `K`.

**What this changes.** The attempt of 2026-09-19 on
`fpbs-hyperbolic-quotient-every-generating-set` left SF undecided on kernels
with trivial centre, naming `F_2 x F_2` and `F_2 x` lamplighter. Both are now
decided negatively, on every generating set.

* **Named invariant.** The commuting cross: an infinite normal `K` whose
  centralizer is infinite modulo `K`.
* **Failing step.** The hypothesis of `thm:hutchcroft1plus2` itself, before
  Appendix A of [CS] begins.
* **Consequence.** No choice of supporting sets, whether built from
  half-spaces of a factor, from WPD elements, or from projections, can feed the
  Choi–Seo route on any direct product. Proofs of (Gamma1) on the product class
  must use another mechanism, such as counting fibres
  (`fpbs-fibre-bubble-forces-mean-field-susceptibility`) or a triangle
  condition (Kozma on `T x T`).

**Consistency check.** [CS] verify SF on acylindrically hyperbolic groups
(`prop:supportingWPD`, artifact). Together with this theorem, that forces the
commuting-cross class to be disjoint from the acylindrically hyperbolic groups.
This agrees with the known fact that acylindrically hyperbolic groups are not
direct products of two infinite groups. It is a check, not part of the proof.

**Scope and limits.**

* This obstructs a method, not a conclusion. `T_4 x Z` has `p_c < p_(2->2)`,
  and hence (Gamma1). So SF is strictly stronger than (Gamma1) on the class.
* Not covered:
  - `Z^2 ⋊ F_2` with a faithful action, where `C_G(Z^2) = Z^2`;
  - `SL_3(Z)`, and irreducible lattices in products;
  - infinite simple groups;
  - groups with only a finite-index product subgroup whose factors are swapped
    by the extension, such as `F_2 wr Z/2`. There the identity mixes the two
    coordinates.
* It says nothing about (Gamma2) or about the percolation Kesten gap
  `fpbs-percolation-kesten-normal-gap`.

**Computation.** `experiments/fpbs-commuting-cross-2026-09-17/` tests
membership in `A A^-1` by brute force over `A`, not through the identity. It
finds every core point bad and `#good < #A/2` in each of these cases:

| Group | Generators | `n` | Core points bad | `#good` | `#A/2` |
| --- | --- | --- | --- | --- | --- |
| `F_2 x F_2` | product | 20 | 400/400 | 68 | 234 |
| `F_2 x F_2` | product | 40 | 1600/1600 | 143 | 871.5 |
| `F_2 x F_2` | mixed | 20 | 400/400 | 92 | 246 |
| `F_2 x D_infinity` | mixed | 20 | 400/400 | 62 | 232 |
| `F_2 x Z` | product | 16 | 256/256 | 30 | 143 |

The mixed generating sets are not Cartesian: on `F_2 x F_2` they include
`(a,a)` and `(ab,b^-1)`, and on `F_2 x D_infinity` they include `(a,s)`.
