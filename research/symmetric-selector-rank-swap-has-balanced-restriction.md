---
rg: 2
id: symmetric-selector-rank-swap-has-balanced-restriction
kind: claim
title: The symmetric selector type contains eight equal-scale rank-swap spin packets
distinct_from:
  symmetric-selector-schur-residual-packet: that packages the rank-fifteen residual and the reset translations in one primitive type; this computes the exact restriction after installing the missing hyperbolic pair.
---

Let `Sigma` be the primitive selected representation from
`symmetric-selector-schur-residual-packet`.  Its representation space has the
canonical form

```text
H_Sigma = H_res tensor l2(X),              |X|=16,       (SBR1)
```

where the common diagonal extraspecial group acts by its rank-fifteen spin
representation `rho` on `H_res`, every product of coordinate centers acts as
the corresponding diagonal sign on `l2(X)`, and `Sym(X)` acts by its natural
permutation representation on `l2(X)`.

Fix a nonzero reset direction `v` and an independent direction `u`.  Split
`X` into the four cosets of `span(u,v)`.  On each four-point coset, install
the two complementary signed-permutation pairs from
`four-point-gauge-orbit-has-balanced-derived-rank-swap`.  Taking their block
products over the four cosets gives ordinary elements of

```text
<product_x J_x, Sym(X)> <= G                             (SBR2)
```

with

```text
[p_-,q_-]=tau_v,
[p_+,q_+]=J_all tau_v,                                  (SBR3)
```

and all cross commutators trivial.  These elements commute with the common
rank-fifteen residual `Delta(H)`.

On one four-point coset, the signed-permutation representation splits as

```text
R_+ direct_sum R_-,                                     (SBR4)
```

where `R_+` and `R_-` are two-dimensional, `J_all=-1`, and `tau_v` acts by
`+1` and `-1`, respectively.  Exactly one of the pairs in `(SBR3)` is a
Pauli pair on each summand.  Hence

```text
Sigma restricted to <Delta(H),p_-,q_-,p_+,q_+>
 =4 (rho tensor R_+) direct_sum 4 (rho tensor R_-).     (SBR5)
```

Both full types in `(SBR5)` have dimension `2^16`, and each restricts to the
common rank-fifteen residual as exactly two copies of `rho`.  The two reset
signs therefore have identical residual restriction multiplicity.  Across
the four gauge squares there are eight full rank-sixteen packets, with no
change of total scale and no additional ambient tensor factor.

Because `(SBR2)` is contained in the same fixed finite group used to define
`Sigma`, the decomposition and its equality of multiplicities persist after
finite-group Hilbert--Schmidt exactification with constants independent of
ambient matrix dimension.
