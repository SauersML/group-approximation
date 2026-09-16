---
rg: 2
id: rordam-line-bundle-sums-are-k-theoretically-rigid
kind: claim
title: Finite sums of Rordam line bundles are determined in K-theory by their index multisets
distinct_from:
  hopf-power-blocks-obey-weighted-hall-euler-criterion: that computes the top Chern (Euler) class of a sum and characterizes when it vanishes; this computes the whole K0 class and proves it determines the multiset and its divisibility, with no Hall or rank hypothesis.
  triangular-hopf-bundles-admit-coherent-dyadic-euler-roots: that exhibits halvable bundle families of the form 2^k L; this proves that within Rordam sums every K0-halving is of that literal multiplicity-doubling form.
  stw99-lxvi-k0-dyadic-divisibility-obstruction: that says a CAR corner forces dyadic divisibility of the class in K0 of the ambient algebra; this computes exactly which Rordam sums over products of two-spheres are divisible.
---

Let `F` be a finite or countably infinite set, `Z_F=(S^2)^F`, let `H` be the
Hopf line bundle on `S^2`, and put `zeta_i` for its pullback along the `i`th
coordinate projection.  For a finite subset `J` of `F` let
`zeta_J = tensor_(i in J) zeta_i` (the trivial line bundle when `J` is empty),
and let `p_J` be a projection in `C(Z_F) tensor K` with range bundle `zeta_J`.
For a finitely supported function `m` from finite subsets of `F` to
nonnegative integers write

```text
zeta(m) = directSum_J zeta_J^(directSum m(J)),     p(m) = directSum_J p_J^(directSum m(J)).
```

Put `b_i=[zeta_i]-1` and `b_S=prod_(i in S) b_i` in `K^0(Z_F)`.  Then:

1. **Expansion.**  The `b_S` (S finite) are linearly independent, span
   `K^0(Z_F)`, satisfy `b_i^2=0`, and
   `[zeta(m)] = sum_S N_m(S) b_S` with `N_m(S)=sum_(J contains S) m(J)`.
2. **Rigidity.**  `[p(m)]=[p(m')]` in `K_0(C(Z_F))` iff `m=m'`.  Hence two
   finite Rordam sums are Murray-von Neumann equivalent iff they are stably
   equivalent iff their index multisets coincide.
3. **Divisibility.**  For `d>=1`, `[p(m)]` lies in `d K_0(C(Z_F))` iff `d`
   divides `m(J)` for every `J`; then the unique `y` with `dy=[p(m)]` is
   `[p(m/d)]`.

In particular, if `e` is a projection over `C(Z_F)` such that the direct
sum of `2^n` copies of `e` is equivalent to `p(m)`, or merely
`2^n[e]=[p(m)]`, then every multiplicity of `m` is divisible by `2^n` and
`[e]=[p(m/2^n)]`.  A nonzero multiplicity-free
Rordam sum (pairwise distinct index sets) is not even divisible by two in
`K_0`.  So any dyadic halving that respects a decomposition into finite
Rordam blocks is literal multiplicity doubling of index sets.  Nothing is
asserted about equivalences in the multiplier algebra of `C(Z_F) tensor K`
that do not respect such a block decomposition.
