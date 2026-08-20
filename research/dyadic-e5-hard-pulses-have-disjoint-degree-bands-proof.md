---
rg: 2
id: dyadic-e5-hard-pulses-have-disjoint-degree-bands-proof
kind: route
title: Frobenius-square the transfer recurrence on powers of two
target: dyadic-e5-hard-pulses-have-disjoint-degree-bands
requires:
  - e5-heisenberg-word-realizes-rank-one-boundary-pulse
---

For a determinant-one `2 by 2` matrix in characteristic two,

```text
tr(A^2)=tr(A)^2.
```

Since `tr(S)=x^2`, for `n=2^k` one has

```text
a_n+d_n=x^(2n).                                          (DHP4)
```

Squaring `S^n` gives

```text
c_(2n)=c_n(a_n+d_n),
d_(2n)=c_n^2+d_n^2.                                      (DHP5)
```

Starting from `c_1=x,d_1=1`, the first recurrence proves
`c_n=x^(2n-1)`.  Put `u_n=d_n+1`.  The second becomes

```text
u_(2n)=x^(4n-2)+u_n^2.                                   (DHP6)
```

Induction now gives `(DHP1)`.

Let `A=S^-n=[[d_n,c_n],[c_n,a_n]]` and represent the hard cross form by
`H=[[1,1],[1,0]]`.  Direct multiplication yields

```text
A H A^T+H=[[d_n^2+1,c_nd_n],[c_nd_n,c_n^2]],             (DHP7)
```

which is `(DHP2)`.  Formula `(DHP1)` shows:

```text
supp(d_n^2+1) subset [2n,4n-4],
supp(c_nd_n)   subset [2n-1,4n-3],
supp(c_n^2)           ={4n-2}.                            (DHP8)
```

The constant term of `d_n` makes `2n-1` occur in the mixed entries, and the
monomial formula for `c_n^2` makes `4n-2` occur uniquely.  Finally the right
endpoint of `B_k` is one less than the left endpoint of `B_(k+1)`, proving
pairwise disjointness and adjacency.
