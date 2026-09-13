---
rg: 2
id: relator-width-survives-abelian-and-central-extensions-proof
kind: route
title: Central layers vanish in the perfectness identity, and abelian layers are spanned by commutators with boundedly many generating relator conjugates
target: relator-width-survives-abelian-and-central-extensions
requires: [perfect-group-relator-width-over-nilpotent-groups]
---

Notation: `[g, h] = g h g^-1 h^-1`. `Cons_k(S)` is the set of products of at most `k` `Q`-conjugates of elements of
`S^(+-1)`, so `Cons_j · Cons_k ⊆ Cons_(j+k)` and `Cons_k` is closed under conjugation and inversion. Write
`R(a) = { r(a) : r in R }`.

## 0. Normal generation

For every finite `Q` and `a in Q^X`, the normal closure of `R(a)` in `<a>` is `<a>`: the quotient is a finite
quotient of `G`. `G` is perfect: its abelianization is finitely generated with no finite quotient, hence `0`.
So the identities `x = c_x rho_x` of the statement exist in `F`. We may assume `Q = <a>`, since conjugators in
`<a>` are conjugators in `Q`.

## 1. Central extensions, item (a)

Let `Z <= Z(Q)` with `Q/Z in 𝒞`, and put `K = K(𝒞)`. Apply the bound in `Q/Z` to the image of `a`, and lift every
conjugator to `Q`. This gives `p_y in Cons_K(R(a))` and `z_y in Z` with `a_y = p_y z_y` for every `y`.

- **Central factors cancel.** For words `u, v`, `u(a) = u(p) z_u` and `v(a) = v(p) z_v` with `z_u, z_v` central.
  So `[u(a), v(a)] = [u(p), v(p)]`, and `c_x(a) = c_x(p)`.
- **Counting.** `v(p)` is a product of `|v|` elements `p_y^(+-1)`, so it lies in `Cons_(K|v|)`. The same holds for
  its conjugate by `u(p)`. So `[u(p), v(p)] = (u(p) v(p) u(p)^-1) · v(p)^-1` lies in `Cons_(2K|v|)`, and `c_x(p)` lies in
  `Cons_(2KL)`.
- **Conclusion.** `a_x = c_x(a) rho_x(a) in Cons_(2KL + L_0)`.

## 2. The spanning lemma

**Lemma.** A finite group `Q` acts by automorphisms on a finite abelian group `A` (written additively, `g.gamma`).
Let `s_1, ..., s_n in Q` be elements whose images generate the image of `Q` in `Aut(A)`. Then
```text
[A, Q] := < gamma - g.gamma : gamma in A, g in Q >  =  (1 - s_1)A + ... + (1 - s_n)A .
```

*Proof.* Each `(1 - s)A` is the image of an endomorphism, hence a subgroup. Put `W = sum_i (1 - s_i)A`, so
`W <= [A, Q]`. Let `A^ = Hom(A, C^x)`, and for `H <= A` let `H^perp` be the characters trivial on `H`. Duality for finite
abelian groups gives `|H| · |H^perp| = |A|`.
- `f` kills `(1 - s)A` iff `f(s.gamma) = f(gamma)` for all `gamma`, that is iff `f` is fixed by `s`.
- So `W^perp` is the set of characters fixed by every `s_i`. That is the set fixed by the image of `Q`, since the
  `s_i` generate it and the fixed characters of a group of automorphisms form the common fixed set of its
  generators.
- The same computation with all `g in Q` shows that `[A, Q]^perp` is that same set.

So `|W| = |A| / |W^perp| = |A| / |[A, Q]^perp| = |[A, Q]|`, and `W = [A, Q]`. No coprimality is used.

**Commutators with an element.** In `Q`, with `A` normal and written multiplicatively, `[gamma, s] = gamma s gamma^-1 s^-1`
is `gamma · (s.gamma)^-1`, the additive `(1 - s)gamma`. It is the product of the conjugate `gamma s gamma^-1` and `s^-1`.
If `s` is a conjugate of `r(a)^(+-1)`, then `[gamma, s] in Cons_2`.

## 3. Abelian extensions, item (b)

Let `A` be abelian and normal in `Q`. Assume the width of the image of `a` is at most `K` in `Q/A` and at most `K'`
in `Q/[A, Q]`.
- **Generating conjugates.** In `Q/A`, each image of `a_x` is a product of at most `K` conjugates of relator
  values. Lift the conjugators to `Q`, and let `s_1, ..., s_n` (`n <= |X| K`) be the resulting conjugates of
  elements `r(a)^(+-1)`. Then `<s_1, ..., s_n> A` contains every `a_x`, so it is `Q`. `A` acts trivially on `A`, so the
  images of the `s_i` generate the image of `Q` in `Aut(A)`.
- **The top.** `[A, Q]` is normal in `Q`. By hypothesis `a_x = P_x e_x` with `P_x in Cons_(K')` and `e_x in [A, Q]`.
- **The bottom.** By the Lemma, `e_x = prod_(i <= n) [gamma_i, s_i]` for some `gamma_i in A`. The factors commute,
  since they lie in `A`. So `e_x in Cons_(2n)`.

Hence `a_x in Cons_(K' + 2|X|K)`. `A/[A, Q]` is central in `Q/[A, Q]` with quotient `Q/A`, so section 1 gives
`K' <= 2LK + L_0` when `Q/A in 𝒞`.

## 4. Abelian-by-nilpotent groups, item (c)

Let `A` be abelian with `B = Q/A` nilpotent.
- **The top.** `Q/[A, Q]` is a central extension of `B`, so it is nilpotent. By
  `perfect-group-relator-width-over-nilpotent-groups` (item 1), `a_x = P_x e_x` with `P_x in Cons_(K_nil)` and
  `e_x in [A, Q]`.
- **Relator values generate.** The images of `R(a)` normally generate `B`, by section 0. In a finite nilpotent
  group every conjugate `s^g = s [s^-1, g]` lies in `s Phi(B)`, because `[B, B] <= Phi(B)`. So the images of `R(a)` generate
  `B` modulo `Phi(B)`, hence generate `B`. `A` acts trivially on `A`, so the `r(a)` generate the image of `Q` in `Aut(A)`.
- **The bottom.** By the Lemma with `s_r = r(a)`, `e_x = prod_(r in R) [gamma_r, r(a)] in Cons_(2|R|)`.

So `a_x in Cons_(K_nil + 2|R|)`.

## 5. Scope

- **Examples.** Coprime `A ⋊ B` with `B` nilpotent. `F_p^n ⋊ U` with `U` a `q`-subgroup of `GL_n(p)`. Abelian
  subgroups of towers under nilpotent tops. None of these needs bounded class, bounded primes or coprimality.
- **Why the constants multiply.** Section 1 expands the commutator part of the perfectness identity, so a
  central layer costs a factor `2L`. `l` layers give constants of order `(2L + 2|X|)^l`. A nilpotent-by-nilpotent
  group whose kernel has unbounded class alternates central and non-central layers without bound, and needs a
  template form of section 1 in which central corrections are made inside fixed pairs.
