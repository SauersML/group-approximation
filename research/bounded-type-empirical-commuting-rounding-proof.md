---
rg: 2
id: bounded-type-empirical-commuting-rounding-proof
kind: route
title: Pass the empirical reflection measures to commuting-support limits
target: bounded-type-noncentral-code-sectors-round-uniformly
requires: []
---

First fix `r<=D`.  Let `R_r` be the compact set of reflections in `M_r`
with normalized Hilbert--Schmidt metric.  A tuple `(q_i)_(i=1)^L` defines
the empirical probability measure

```text
 mu=L^(-1)sum_i delta_(q_i)
```

on `R_r`, and its complete-pair energy is the continuous functional

```text
 e(mu)=integral integral ||[x,y]||_2^2 dmu(x)dmu(y).      (BTE1)
```

Suppose no modulus in `(BTN3)` existed.  A sequence with `e(mu_n)->0` and
a fixed positive distance from every commuting tuple has a weakly
convergent subsequence `mu_n->mu`.  Continuity in `(BTE1)` gives `e(mu)=0`.
Every two points of `supp(mu)` commute: otherwise continuity gives
neighborhoods of positive `mu` measure on which the integrand is bounded
below, contradicting zero energy.

The continuous function `x |-> dist(x,supp(mu))^2` has integral tending to
zero under `mu_n`.  Replace each atom `q_i` by a nearest reflection in
`supp(mu)`.  All replacements commute and their average squared movement
tends to zero, the desired contradiction.  Taking the worst modulus over
the finitely many `r<=D` proves the fixed-block assertion.

For `(BTN1)`, perform this construction on every central block.  Replace the
fixed-block modulus by a bounded concave majorant.  Jensen's inequality
then bounds the central trace average of the correction by the same modulus
evaluated at `(BTN2)`, proving `(BTN3)` without dependence on the number or
multiplicity of blocks.

Finally, telescoping a bounded parity word after the first correction and
using bounded coordinate occurrence shows that the commuting tuple `(S_i)`
has average parity defect `O(eta+omega_D(beta))`.  Simultaneously diagonalize
it.  On each joint atom, squared defect of a parity word is four times its
binary syndrome indicator.  Classical LTC soundness moves that atom's word
to the code with proportional average Hamming cost.  Applying the correction
atom by atom inside the same joint PVM proves `(BTN4)`.
