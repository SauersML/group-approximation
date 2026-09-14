---
rg: 2
id: linear-sofic-kl-from-amplified-algebraic-roots
kind: claim
title: Amplified approximate roots over an extension field force Kervaire--Laudenbach for every linear sofic group over the base field
distinct_from:
  kervaire-laudenbach-holds-for-hyperlinear: that is the unconditional theorem for unitary ultraproducts, where compactness of U(n) supplies exact roots by degree theory; this is a conditional transfer through rank-metric ultraproducts, where no compact form exists and the root premise is a separate algebraic statement.
  nonsingular-adjunction-preserves-approximation-radicals: that bounds the kernel of the adjunction inside the MF and hyperlinear radicals; this proves injectivity outright for rank-metric approximable coefficient groups, given a root premise.
  schur-kernel-lies-in-char-p-linear-sofic-radical: that is a degree-two Schur-kernel statement for central extensions; this is the degree-one injectivity statement for the coefficient group itself.
artifacts:
  - research/artifacts/ideas-nonhyperlinear-2026-09-13.md
---

**ESTABLISHED** through
`linear-sofic-kl-from-amplified-roots-ultraproduct-proof` (direct proof, no
external inputs beyond the definitions).

**Definitions.** For a matrix `x` in `M_n(L)` put `rho(x) = rank(x)/n`.
Following Arzhantseva--Paunescu (arXiv:1212.6780, Definitions
`universallinearsofic` and `def:lsofic`, the latter stated over `C`), a
countable group `G` is `F`-linear sofic if there is an injective homomorphism

```text
Theta : G --> Pi_{i -> omega} GL_{n_i}(F) / d_omega ,
```

the quotient of the Cartesian product by the normal subgroup of sequences
`(a_i)` with `lim_omega rho(a_i - 1) = 0`.

**Root premise `ARR(L)`** for a field `L`: for every `n >= 1`, every finite
tuple `a = (a_1, ..., a_k)` in `GL_n(L)^k`, every word `w` in `F_k * <t>`
whose exponent sum in `t` is nonzero, and every `epsilon > 0`, there are
`r >= 1` and `T` in `GL_{nr}(L)` with

```text
rho( w(T ; a_1 (x) 1_r, ..., a_k (x) 1_r) - 1 )  <=  epsilon .
```

**Theorem.** Let `F <= L` be fields with `ARR(L)`. For every countable
`F`-linear sofic group `G` and every `w` in `G * <t>` with nonzero exponent
sum in `t`, the coefficient map `G --> (G * <t>)/<<w>>` is injective.

**Scope.** Exact roots (`epsilon = 0`) are not needed, and the amplification
`r` may depend on the tuple. `ARR(C)` holds with `r = 1` and exact roots for
unitary tuples, by the Gerstenhaber--Rothaus degree argument recorded in
`kervaire-laudenbach-holds-for-hyperlinear`; for general tuples, and in
positive characteristic, `ARR` is the OPEN claim
`amplified-algebraic-roots-for-nonsingular-equations`. Exact roots in
characteristic 2 genuinely need `r > 1` in degree two, see
`char-two-jordan-square-root-needs-amplification`.
