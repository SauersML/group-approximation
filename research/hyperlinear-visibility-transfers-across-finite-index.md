---
rg: 2
id: hyperlinear-visibility-transfers-across-finite-index
kind: claim
title: An element is tracially visible in a group exactly when it is visible in a finite-index subgroup containing it
distinct_from:
  hyperlinear-elementwise-visibility: that claim characterizes hyperlinearity of one group by visibility of each of its elements; this one compares visibility of one fixed element in a group and in a finite-index subgroup, losing the index in the constant.
  mf-finite-normal-tracially-visible: that claim makes elements of a finite normal subgroup of an MF group visible; this one transports visibility along a finite-index inclusion for arbitrary countable groups, with no MF hypothesis.
---

**Statement.** Let `G` be a countable group, `H <= G` a subgroup of finite
index `m`, and `g != 1` in `H`. Use "tracially visible" in the sense of
`hyperlinear-elementwise-visibility`: there is `c>0` such that for every
finite `F` and every `delta>0` some unitary map `phi` into `U(d)` has
normalized Hilbert--Schmidt multiplication defect at most `delta` on `F` and
`Re tr_d(phi(g)) <= 1-c`.

1. If `g` is tracially visible in `G` with constant `c`, it is tracially
   visible in `H` with constant `c`.
2. If `g` is tracially visible in `H` with constant `c`, it is tracially
   visible in `G` with constant `c/m`.

So the set of nontrivial elements of `H` that are not tracially visible in
`H` is exactly the set of nontrivial elements of `H` that are not tracially
visible in `G`.

No novelty is claimed. Part 2 is the elementwise form of the standard fact
that a group containing a hyperlinear finite-index subgroup is hyperlinear.
Bachner--Dogon--Lubotzky use that fact in arXiv:2508.17392v3, source line 488:
"As $\Lambda \leq \Gamma$ has finite index, it follows that $\Gamma$ is
hyperlinear as well."
