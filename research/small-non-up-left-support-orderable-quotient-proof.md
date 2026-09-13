---
rg: 2
id: small-non-up-left-support-orderable-quotient-proof
kind: route
title: Follow second expressions from an extreme element of the support to a relator whose letters an ordering cannot balance
target: small-non-up-left-support-has-no-orderable-quotient
requires: []
---

We prove the sieve first, since the main statement is a special case.

**Setup.** Let `X`, `G_X`, `m`, `n` be as in the claim. Suppose
`rho: G_X -> G` is a homomorphism into a torsion-free group that is injective
on `{a_i}` and on `{b_j}`. Let `phi: <a_1, ..., a_m> -> L` be a homomorphism
into a left-ordered group. We show that `i -> phi(a_i)` attains its minimum
at no fewer than three indices, and likewise its maximum.

(1) **Choice of partners.** Fix `i_0` with `phi(a_(i_0))` minimal. For each
`j` choose a partner `(c(j), p(j)) != (i_0, j)` of `(i_0, j)`, so that
`a_(i_0) b_j = a_(c(j)) b_(p(j))` in `G_X`. If `c(j) = i_0`, then
`b_j = b_(p(j))` in `G_X`, hence `rho(b_j) = rho(b_(p(j)))`, hence `p(j) = j`
by injectivity. That contradicts `(c(j), p(j)) != (i_0, j)`. So
`c(j) != i_0` for every `j`.

(2) **A relator.** Iterating `p` on the finite set `[n]` reaches a cycle
`j_0, j_1 = p(j_0), ..., j_k = j_0` with `k >= 1`. Put `c_t = c(j_t)` and
`u_t = a_(c_t)^-1 a_(i_0)`. The partner relation gives
`u_t = b_(j_(t+1)) b_(j_t)^-1`, so in `G_X`

```text
u_(k-1) ... u_1 u_0 = b_(j_k) b_(j_0)^-1 = 1.                  (R)
```

Each `u_t` lies in `<a_1, ..., a_m>`, so `phi` applies to `(R)`.

(3) **Two letters.** Suppose every `c_t` equals one index `c`. Then `(R)`
reads `(a_c^-1 a_(i_0))^k = 1` in `G_X`, hence in `G`. As `G` is
torsion-free, `rho(a_c) = rho(a_(i_0))`, so `c = i_0` by injectivity. That
contradicts (1). So at least two distinct indices occur among the `c_t`, and
none of them is `i_0`.

(4) **The ordering.** By minimality `phi(a_(i_0)) <= phi(a_(c_t))`.
Left-multiplying by `phi(a_(c_t))^-1` gives `phi(u_t) <= 1`. Put
`w_t = phi(u_(k-1)) ... phi(u_t)`. Then `w_(k-1) = phi(u_(k-1)) <= 1`, and
`w_t = w_(t+1) phi(u_t) <= w_(t+1)` by left invariance, with strict inequality
when `phi(u_t) < 1`. So `w_0 <= 1`, and `w_0 = 1` only if every `phi(u_t) = 1`.
By `(R)`, `w_0 = phi(1) = 1`. Hence `phi(a_(c_t)) = phi(a_(i_0))` for all `t`.

By (3) and (4) the minimum is attained at `i_0` and at no fewer than two
further indices. Reversing the order of `L` gives another left order, and
the same argument gives the maximum.

**Sieve.** If `phi` is not constant on the indices, the minimum and maximum
fibres are disjoint, so `m >= 6`. If `m <= 5`, `phi` is constant, so
`phi(a_i) = phi(a_1) = 1` for all `i`, and `phi` is trivial on
`<a_1, ..., a_m>`. A homomorphism `G_X -> Q` restricts to one on
`<a_1, ..., a_m>`, and `Q` is ordered. This proves the sieve.

**Main statement.** Let `A = {a_1 = 1, a_2, ..., a_m}` and
`B = {b_1, ..., b_n}` be as in the claim, with the elements listed without
repetition. Right-translating `B` changes neither the multiplicities in
`AB` nor `<A>`, so assume `b_1 = 1`. Let `X` be the set of quadruples
`(i,j,k,l)` with `a_i b_j = a_k b_l` in `G`. Every pair has a partner,
because `AB` has no unique product. The obvious map `rho: G_X -> G` is
injective on the generators `a_i` and `b_j`. It maps `<a_1, ..., a_m>` onto
`H`, so every `phi: H -> L` pulls back. A fibre of `i -> phi(rho(a_i))` is a
fibre of `phi` on `A`, since the `a_i` are distinct. Items 1 to 3 follow.

For the consequences with `|A| <= 5`: `Z`, free groups, torsion-free
nilpotent groups and subgroups of `Homeo^+(R)` are left-orderable, so every
homomorphism into them is trivial. `H` is finitely generated, so infinite
abelianization would give a nontrivial homomorphism to `Z`. `H != 1`, since
`A = {1}` makes every product in `AB` unique. So `H` is not locally
indicable.

For `<B>`: `(AB)^-1 = B^-1 A^-1`, and inversion matches expressions
bijectively. So `B^-1 A^-1` has no unique product, `1 in B^-1` and
`<B^-1> = <B>`.

**Zero divisors.** If `alpha beta = 0` with `alpha, beta != 0` over a field,
then a unique expression `s = gh` with `g in supp alpha` and
`h in supp beta` would give `s` the nonzero coefficient
`alpha(g) beta(h)` in `alpha beta`. So `supp alpha supp beta` has no unique
product. Fix `a_0 in supp alpha` and `b_0 in supp beta`. Then
`A = a_0^-1 supp alpha` and `B = (supp beta) b_0^-1` contain `1`, and
`AB = a_0^-1 (supp alpha supp beta) b_0^-1` has no unique product. Also
`<A> = <a^-1 c : a, c in supp alpha>` and
`<B> = <b c^-1 : b, c in supp beta>`.

**Left-orderable groups.** If `H` itself is left-ordered and `phi` is the
identity, fibres of `phi` on `A` are singletons, contradicting item 1. So no
pair without unique products lies in a left-orderable group.

QED
