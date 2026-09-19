---
rg: 2
id: norm-corona-sparse-character-centralizer-proof
kind: route
title: Slow the character-window diagonal so its full cylinder projection centralizes every prescribed lift
target: norm-corona-sparse-character-atom-reduces-pointwise-centralizer
requires: []
---

Enumerate `A=<a_0,a_1,...>` and lift `rho(a_j)` and `b_k` to unitary
sequences `U_(j,n)` and `W_(k,n)`.  For every fixed `m`, the first `m+1`
involutions commute modulo the direct sum and hence can, on a sufficiently
late tail, be perturbed to exact commuting involutions

```text
V_(0,n),...,V_(m,n).                                  (SCR4)
```

Because each `[b_k,rho(a_j)]` is zero, the tail can simultaneously be chosen
so that, for `j,k<=m`, the perturbation errors and the sums

```text
sum_(j<=m) ||[W_(k,n),V_(j,n)]||                      (SCR5)
```

are at most `1/m`.  Choose a window size `m=m(n)->infinity` slowly enough
that these bounds hold at every selected coordinate.

The negative spectral projection of `rho(a_0)` is nonzero.  After passing to
an infinite coordinate subsequence, `V_(0,n)` has a nonzero negative
eigenspace.  At each such coordinate choose one nonzero **full joint
eigenspace projection**

```text
P_n=product_(j<=m(n)) (1+epsilon_(j,n)V_(j,n))/2,
epsilon_(0,n)=-1.                                    (SCR6)
```

Set `P_n=0` off the subsequence.  Repeated subsequence extraction makes every
fixed sign `epsilon_(j,n)` eventually constant; the limiting signs define a
character `chi` with `chi(a_0)=-1`.  Since `||P_n||=1` on infinitely many
coordinates, `P=[P_n]` is nonzero, and the perturbation bounds give `(SCR1)`.

Finally, a product commutator telescopes without any rank or trace factor:

```text
||[W_(k,n),P_n]||
 <= (1/2) sum_(j<=m(n)) ||[W_(k,n),V_(j,n)]||.         (SCR7)
```

For every fixed `k`, `(SCR5)` and the slow diagonal make the right side tend
to zero.  Hence `[P,b_k]=0` in `Q`, proving `(SCR3)` for the whole prescribed
countable family.

