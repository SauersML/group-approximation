---
rg: 2
id: periodic-higman-bs-clocks-have-three-opnorm-small-seams-proof
kind: route
title: Match the 3-power clock spectra by their ordered eigenvalue lists
target: periodic-higman-bs-clocks-have-three-opnorm-small-seams
requires: []
---

The relation `(HOC1)` follows directly.  Since multiplication by `2` is
invertible modulo `q=3^n`,

```text
P D P^(-1)e_x=exp(2 pi i (2x)/q)e_x=D^2e_x.
```

It remains to prove the operator-norm matching estimate.

For `1<=m<=n`, the residues of additive order `3^m` form one orbit under
multiplication by `2`: their number is

```text
phi(3^m)=2*3^(m-1),
```

and `2` has exactly that multiplicative order modulo `3^m`.  For completeness,
this last fact follows from the lifting-the-exponent identity

```text
v_3(2^(2*3^r)-1)=v_3(4-1)+v_3(3^r)=r+1:
```

the power `2*3^(m-1)` is trivial modulo `3^m`, whereas the preceding
`3`-divisor of that power is not.  Together with
the fixed residue zero, the spectrum of `P_n`, with multiplicity, is therefore

```text
{1} multiset-union
  union_(m=1)^n {all (2*3^(m-1))-th roots of unity}.  (HOP1)
```

The cardinalities sum to

```text
1+sum_(m=1)^n 2*3^(m-1)=3^n=q.
```

Write the arguments in `[0,1)` of the multiset `(HOP1)` in increasing order
as `a_1<=...<=a_q`, and write `b_k=(k-1)/q` for the arguments of the spectrum
of `D_n`.  For `0<t<1`, the number of points of `(HOP1)` in `[0,t)` is

```text
1+sum_(m=1)^n ceil(2*3^(m-1)t).
```

The elementary inequalities for ceilings show that this count is at least
`ceil(qt)` and exceeds it by at most `n+1`.  Hence the two ordered counting
functions differ by at most `n+1`, and monotonicity against the `q`-point
uniform grid gives

```text
|a_k-b_k| <= (n+2)/q                 (1<=k<=q).        (HOP2)
```

Choose an eigenbasis of `P_n` ordered by the `a_k`, and let `H_n` send it to
the standard eigenbasis of `D_n` ordered by the `b_k`.  Both conjugated
matrices are diagonal in that basis, so `(HOP2)` and
`|exp(2 pi i s)-exp(2 pi i t)|<=2 pi |s-t|` give `(HOC2)`.

For the gauged packets, the relative gauge at each of the first three
interfaces is `G_(j-1)^*G_j=H_n`.  Their seam is exactly the left side of
`(HOC2)`.  At the cyclic interface the relative gauge is `H_n^(-3)`.
Insert the approximation `D_n approximately H_n P_n H_n^*` and conjugate by
`H_n^(-4)` to obtain `(HOC4)` by the triangle inequality.

Finally, the permutation underlying `P_n` has an orbit of even length
`2*3^(n-1)`, so `-1` is an eigenvalue of `P_n`.  Therefore

```text
||P_n-1||_op=2,
```

and unitary conjugacy proves `(HOC3)`.  The construction pays no estimate on
the return term `(HOC4)`, so it proves exactly the three-seam statement and
does not assert a full Higman microstate.
