---
rg: 2
id: nonhyperlinear-from-pauli-tail-dichotomy
kind: route
title: Either the Pauli blocks branch or they are rigid, and both are contradictions
target: non-hyperlinear-group
requires:
  - atlas-steinberg-rank-five-translation
  - pauli-block-tail-or-flat-rigidity-dichotomy
  - constant-block-contraction-gap
  - fractional-source-branch-pressure
  - soft-block-mass-yields-fractional-branch
---

`atlas-steinberg-rank-five-translation` fixes the explicit finite atlas group
`Gamma_St`.  Suppose it were hyperlinear, and take trace-preserving
finite-dimensional microstates with atlas relator defect `delta_n -> 0`.  Pass
to the fixed two-qubit raw/comb Pauli packet and write its comb compression as
a contraction `T_n=(T_(ij,n)) in M_4(N_n)`, whose sixteen block masses are
exactly `1/8` by `TRUE_DOUBLE_PAULI_COMB_IS_FOURIER_FLAT.md` after exactifying
the fixed packet.

Apply `pauli-block-tail-or-flat-rigidity-dichotomy` to each `n` and pass to a
subsequence on which the same branch holds for all `n`; there are only two
branches, so such a subsequence exists.

**Branch `(FLAT)`.**  The dichotomy supplies `C_n in N_n` with

```text
(1/4) sum_(i,j) ||T_(ij,n) - C_n/2||_(2,N_n)^2 <= C delta_n^c -> 0,
```

which by `(CBG1)` is `||T_n - K(C_n)||_2 -> 0`.  This is the hypothesis
`(CBG4)` of `constant-block-contraction-gap`, whose `(CBG5)` then gives

```text
liminf_n ||T_n - K(C_n)||_2^2 >= 3/4 - 1/sqrt(2) > 0,
```

a contradiction.  Note `T_n` is a compression of a group unitary and hence an
operator-norm contraction, which is the only hypothesis `(CBG2)` needs.

**Branch `(TAIL)`.**  The dichotomy supplies a state `P_i` of the fixed family
whose thresholded coverages satisfy `sum_j c_(ij)(t) > 1` with leakage and
ordered-pair Gram energy `O(delta_n^c)`.  By `(SBM3)` and `(SBM4)` of
`soft-block-mass-yields-fractional-branch` those coverages are realized by
partial isometries with zero leakage and controlled Gram energy, so the
one-state instance of `fractional-source-branch-pressure` applies: with
`B = [sum_j c_(ij)(t)] = [1+kappa]`, `y=1`, `(FSB3)` gives

```text
kappa tau(P_i) <= eta^(n) -> 0,
```

while `tau(P_i)` is bounded below by the canonical regular-character mass of the
Pauli cell.  Contradiction again.

Both branches contradict `delta_n -> 0`, so `Gamma_St` is not hyperlinear.

This route and `nonhyperlinear-from-fractional-pauli-pressure` share the
fractional-pressure machinery but not their premise: this one needs no return
network at all, because the dichotomy asserts that *failure* to branch is itself
fatal.  It is the strictly more ambitious premise, since `(FLAT)` currently
rests on the unproved flat-to-common-block step recorded in that node's
Attempts.
