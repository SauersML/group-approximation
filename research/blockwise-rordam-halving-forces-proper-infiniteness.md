---
rg: 2
id: blockwise-rordam-halving-forces-proper-infiniteness
kind: claim
title: Blockwise K0-halving of an infinite Rordam sum with bounded relative support makes it dominate the unit
distinct_from:
  dyadic-rordam-identical-pairing-destroys-sdr: that assumes the branch list contains two identical copies of a branch and concludes failure of Hall; this assumes only that the output sum is 2^n-divisible in K0 block by block, derives the repeated index sets from K-theory, and concludes that the unit is subequivalent to the output projection.
  uniformly-doubled-rordam-steps-force-proper-infiniteness: that assumes a design which duplicates the entire branch list, so multiplicities are given; this derives the multiplicities from arbitrary blockwise K0-divisibility and needs no duplicated branch list.
  one-cofinal-rank-amplifying-branch-forces-proper-infiniteness: that uses rank growth along one distinguished branch continuation; this uses no rank growth of individual summands, only divisibility of finite blocks of rank-one summands.
  rordam-line-bundle-sums-are-k-theoretically-rigid: that is the purely topological K0 computation; this is its multiplier-algebra consequence for infinite sums.
---

Let `Z=(S^2)^N`, `A=C(Z) tensor K`, and let `p_K in A` be a rank-one
projection with range bundle `zeta_K=tensor_(i in K) zeta_i` for each finite
`K subset N`, as in `rordam-line-bundle-sums-are-k-theoretically-rigid`.
Let `(s_j)` be isometries in `1 tensor B(l^2) subset M(A)` with orthogonal
ranges and `sum_j s_j s_j^* = 1` strictly, let `(K_j)_(j in N)` be finite
subsets of `N`, and put

```text
Q = sum_j s_j p_(K_j) s_j^*        (strictly convergent, in M(A)).
```

Fix `n>=1` and suppose:

* **(H1) blockwise divisibility.**  The index set `N` of the `j` is
  partitioned into finite blocks
  `B_1,B_2,...` such that each finite sum
  `q_k=sum_(j in B_k) s_j p_(K_j) s_j^*` has class in `2^n K_0(A)`; for
  example when `q_k` is equivalent to a direct sum of `2^n` copies of one
  projection `e_k` over `A`.
* **(H2) bounded relative support.**  For some finite `C subset N` and some
  integer `s<2^n`, infinitely many distinct sets `K` occurring among the
  `K_j` satisfy `|K \ C| <= s`.

Then `1_(M(A))` is Murray-von Neumann equivalent to a subprojection of `Q`.
Consequently `Q` is full and properly infinite in `M(A)`, and the constant
rank-one projection `g=p_(empty)` satisfies `g <~ Q`, so Rordam's
finiteness certificate `g` not `<~ Q` is unavailable.

**Transported singleton seeds.**  Let branches act on finite sets by
`alpha_beta(J)=nu_beta(J \ E_beta) union I_beta` with `E_beta, I_beta` finite
and `nu_beta : N -> N` injective, and let `a_i` be distinct.  For every
finite branch history `h`, there are a finite set `C_h` and a cofinite set
of indices `i` for which `h({a_i}) = C_h union {u_i}` with pairwise distinct
`u_i` outside `C_h`.  Hence if infinitely many of these transported sets
occur among the `K_j`, (H2) holds with `s=1`, and any blockwise
`K_0`-halving (`n=1`) of the output sum already forces the conclusion.
This covers every halving that pairs outputs block by block, whether or not
the paired outputs come from identical branch copies.
