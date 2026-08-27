---
rg: 2
id: power-pair-pro-p-cyclic-syllable-proof
kind: route
title: Compare p-adic exponents in the abstract free product of procyclic factors
target: power-pair-pro-p-graph-has-gcd-saturation
requires: []
---

Regard `Fhat_p` as the free pro-`p` product of its procyclic factors
`<x_i> ~= Z_p`.  The natural abstract free product

```text
R_p = *_(i=1)^r Z_p
```

embeds in this free pro-`p` product.  Indeed, for any nontrivial reduced word
in `R_p`, reduce the finitely many nonzero `p`-adic syllables modulo a large
enough power of `p`; the word remains reduced in a free product of finite
cyclic `p`-groups, and that free product is residually `p`.  Consequently
ordinary free-product normal forms may be compared inside `Fhat_p`.

Write a nonidentity `u in F` in cyclic-syllable normal form

```text
u=x_(i_1)^(a_1) ... x_(i_s)^(a_s),
a_j in Z\{0},                  i_j!=i_(j+1).             (PPGCD2)
```

Since `p` divides neither exponent, both power substitutions are
automorphisms of `Fhat_p`: their maps on the Frattini quotient are invertible.
Inside `R_p`, therefore,

```text
beta(u)=x_(i_1)^((n/m)a_1) ... x_(i_s)^((n/m)a_s),      (PPGCD3)
```

where `1/m` is taken in `Z_p`.  All displayed exponents are nonzero, so this
word is reduced.  If it equals `v in F`, uniqueness of the abstract
free-product normal form forces the same factor sequence and integer
exponents `b_j` satisfying

```text
m b_j=n a_j.                                            (PPGCD4)
```

Write `m=d m_0`, `n=d n_0` with `gcd(|m_0|,|n_0|)=1`.
Equation `(PPGCD4)` gives integers `c_j` with
`a_j=m_0 c_j` and `b_j=n_0 c_j`.  For

```text
a=x_(i_1)^(c_1)...x_(i_s)^(c_s)
```

this says `u=phi_(m/d)(a)` and `v=phi_(n/d)(a)`.  The converse inclusion is
immediate, as is the identity case, proving `(PPGCD1)`.
