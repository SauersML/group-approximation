---
rg: 2
id: rf-hnn-coefficient-telescope-proof
kind: route
title: Separate every iterated coefficient support and use one HNN wrap block
target: rf-hnn-telescope-retains-coefficient-residual
requires:
  - one-compressor-covariance-has-free-hs-telescope
  - one-bounded-type-coefficient-separates-unbounded-exits
---

At depth `L`, residual finiteness supplies one finite quotient of `Lambda`
which is injective on the support of every `alpha^j(b)`, `0<=j<L`, and on
the corresponding iterates of any requested finite base window and packet.
Use its regular representation `rho_L` and put `rho_L o alpha^j` on block
`j` of the length-`L` covariance telescope.

The cyclic stable-letter shift fails covariance only on the wrap block, so
each HNN generator defect is at most `2/sqrt(L)`.  On the other hand, support
injectivity and the regular trace show on every block that

```text
||rho_L(alpha^j(b))||_2^2=sum_g |c_g|^2
```

when `b=sum_g c_g g`.  Hence the whole telescope retains exactly the
canonical `L2` norm of `b`, independently of `L`.  Separating nonidentity
iterates of a finite word window makes all its base traces canonical, and
injectivity on a finite packet retains every packet projection trace.

For `b=z(1-a)`, the regular representation kills the bounded-type central
projection approximated by `a`; therefore the retained norm is at least
`(1-epsilon)sqrt(tau_B(z))`.  The coefficient stays macroscopically visible
while the total HNN energy is `O(1/L)`, proving the bare self-copy fence.
