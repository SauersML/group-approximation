---
rg: 2
id: compressor-fixed-site-growth-infinite
kind: claim
title: Elementary compressors gain infinitely many Gamma-fixed sites
distinct_from:
  compressor-growth-index-homomorphism: That is an operator-algebra invariant and its multiplicative law; this is a purely combinatorial fact about the Kun--Thom coset space and its translates, proved from nonnegativity of monomial substitutions, with no algebra in it.
  finite-site-orbits-invariant-clifford-kernel: That concerns finite site orbits and the kernel they generate in an invariant Clifford model; this counts the Gamma-fixed sites gained under one compressor and shows the gain is infinite.
artifacts:
  - notes/TRUE_RELATIVE_WALL_IS_COMMUTANT_GROWTH.md
---

For the Kun--Thom Theorem E pair
`Gamma=EL_r(F_q[x_1..x_d]) < G=EL_r(F_q[x^(+-1)]) semidirect SL_d(Z)`,
`d>=3`, let `X=G/Gamma` and let

```text
X^Gamma={g Gamma : g^(-1) in P_Gamma}
```

be the set of `Gamma`-fixed sites.  Then for the positive elementary
transvections `u_13` and `u_32`,

```text
#(u_13 X^Gamma \ X^Gamma)=#(u_32 X^Gamma \ X^Gamma)=infinity.
```

The proof needs only the elementary equivalence, for `nu in SL_d(Z)`,

```text
(1,nu) in P_Gamma  <=>  nu has nonnegative entries,
```

together with the witnesses `g_n=(1,(I+n e_12)^(-1))`, respectively
`g_n=(1,(I+n e_13)^(-1))`, whose images under the compressor leave `X^Gamma`
because one matrix entry turns negative.

**Use.**  In a lamp model over the `G`-set `X`, a site operator `c_y` lies in
`M cap pi(Gamma)'` exactly when `y in X^Gamma`, since `Ad u_gamma(c_y)=c_(gamma y)`
and distinct sites carry distinct operators.  So the displayed difference sets
say that `M cap pi(u_13 Gamma u_13^(-1))'` contains infinitely many site
operators absent from `M cap pi(Gamma)'`, and likewise at `u_32`: the
inclusion grows by an infinite tensor-independent family, not by a
finite-dimensional amount.  This exhibits the model-side mechanism behind the
infinite-index demand of `commutator-compressor-carries-no-wall`.

Two scope notes.  The identification of the growth index with
`2^(#(s X^Gamma \ X^Gamma))` is *not* claimed: that would need the full
relative commutant of the crossed product, which is not computed here, and
index is not monotone under passing to intermediate subalgebras.  And the
statement holds for every invariant graph, because the fixed-site set is
determined by the `G`-set alone and does not involve the adjacency form.
