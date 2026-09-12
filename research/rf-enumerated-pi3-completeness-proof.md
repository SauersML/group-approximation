---
rg: 2
id: rf-enumerated-pi3-completeness-proof
kind: route
title: Profinite closure of an initial-segment subgroup of a free group decides residual finiteness of a central HNN extension
target: residual-finiteness-of-enumerated-presentations-is-pi3-complete
requires:
  - second-level-rice-theorem-for-local-approximation-properties
---

## Upper bounds

For a countably generated recursive presentation `P` of `G`,

```text
G is RF  iff  for all words w:  w = 1 in G
                 or  exists a finite group Q and a homomorphism
                     phi : F(N) -> Q with phi(r) = 1 for every relator r
                     and phi(w) != 1.
```

The first disjunct is `Sigma^0_1`.  For the second, a homomorphism from the
free group on countably many generators to a finite `Q` is an infinite
object, but `Q^N` is compact: such a `phi` exists iff for every `n` there
is a map on the generators `0, ..., n` under which every relator involving
only those generators dies and `w` survives.  "Every relator involving only
generators `<= n` dies" is `Pi^0_1`; the finite disjunction over maps is
`Pi^0_1`; the universal quantifier over `n` keeps `Pi^0_1`; the existential
over the finite group `Q` (given by its multiplication table) makes it
`Sigma^0_2`.  So the matrix is `Sigma^0_2` and `RF_enum` is `Pi^0_3`.  For
finitely generated recursive presentations the compactness step is not
needed: `exists Q, phi` with `for all j, phi(r_j) = 1` is directly
`Sigma^0_2`.  For finite presentations the relator check is finite, the
matrix is `Sigma^0_1`, and `RF_fp` is `Pi^0_2`.

## Lower bounds for the two lower syntaxes

Residual finiteness is hereditary, contains every residually finite group,
and fails for the finitely presented group `BS(2,3)`.  Clauses (a) and (b)
of [[second-level-rice-theorem-for-local-approximation-properties]] use
only heredity and a finitely presented forbidden seed (the marked-group
cover is not needed when the seed is already finitely presented), so
`RF_fp` is `Sigma^0_1`-hard and `RF_rec2` is `Pi^0_2`-hard.

## The third-level family: (RF3)

Let `A = < a_j : j < |W_c| >`.  The elements `a_j = b^j a b^-j`, `j in Z`,
form a free basis of the normal closure of `a` in `F`, so `A` is free on
its listed generators and

```text
H_c = F *_A (A x <s>) = < F, s | [s, A] = 1 >
```

is an HNN extension of `F` with stable letter `s` and both associated
subgroups equal to `A`, the identity isomorphism.  Britton's lemma applies.

**Finite case.**  If `|W_c| = k`, then `A` is finitely generated, hence
closed in the profinite topology of `F` (M. Hall).  Let `g != 1` in `H_c`
be Britton-reduced, `g = f_0 s^{e_1} f_1 ... s^{e_m} f_m`, so that
`f_i notin A` at every pinch position.  Because `A` is closed there is a
finite-index normal subgroup `N` of `F` with `f_i notin A N` for those
finitely many `f_i`, and with `f_0 notin N` if `m = 0`.  Write
`psi : F -> Q = F/N`.  The relations `[s, A] = 1` are respected by
`psi`, so `psi` extends to `H_c -> Q *_{psi(A)} (psi(A) x Z)`.  The image
of `g` is Britton-reduced there, hence nontrivial, and the target is the
fundamental group of a finite graph of finite groups, hence virtually free,
hence residually finite.  So `g` survives in a finite quotient of `H_c`.

**Infinite case.**  Now `A = < a_j : j >= 0 >`.  Let `U` be any finite-index
subgroup of `F` containing `A`, and let `n >= 1` with `b^n in U` (the
order of `b` modulo the core of `U`).  Then

```text
a_{-1} = b^-1 a b = b^-n a_{n-1} b^n  in U,
```

since `n - 1 >= 0`.  So `a_{-1}` lies in the profinite closure of `A`,
while `a_{-1} notin A` because `A` is the free factor on nonnegative
indices.  Put `g = [s, a_{-1}]`.  By Britton `g != 1` in `H_c`.  For any
homomorphism `chi` from `H_c` to a finite group, `U = {f in F : chi(f) in
chi(A)}` is a finite-index subgroup of `F` containing `A`, so
`chi(a_{-1}) in chi(A)` commutes with `chi(s)`, and `chi(g) = 1`.  Thus
`H_c` is not residually finite.

## Assembly

`FIN` is `Sigma^0_2`-complete uniformly, so for every `Pi^0_3` predicate
`S(e) = for all x, exists y, for all z, R(e,x,y,z)` there is a computable
`g` with `[exists y, for all z, R(e,x,y,z)] iff W_g(e,x) finite`.  Put
`G_e = *_x H_g(e,x)`, the countable free product, whose presentation is the
disjoint union of the presentations (RF2) and is recursively enumerated
uniformly in `e`.  Free products of residually finite groups are
residually finite (Gruenberg), and every factor embeds, so
`G_e` is residually finite iff every `H_g(e,x)` is iff `S(e)`.  Hence
`RF_enum` is `Pi^0_3`-hard, and with the upper bound `Pi^0_3`-complete;
complements give the `Sigma^0_3` statement.
