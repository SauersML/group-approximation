---
rg: 2
id: nonhyperlinear-normal-augmentation-corner-kills-mf-proof
kind: route
title: Spectrally cut the unavoidable nontrivial-type corner and normalize by its own rank
target: nonhyperlinear-normal-augmentation-corner-kills-mf
requires: []
---

Fix an arbitrary homomorphism `theta` as in `(NAC3)` and write the norm matrix
corona as `Q`.  Linear extension gives a star homomorphism `C[G]->Q`.
Normality of `K` makes `e_K`, hence `q_K`, central in `C[G]`.  We prove that
`theta` kills `K`.

## Any surviving augmentation complement gives the forbidden trace

Suppose first that

```text
theta(q_K) != 0.                                             (NAC5)
```

Since it is a nonzero projection in a C-star algebra,
`||theta(q_K)||=1`.  We now show that this alternative is impossible.

## Lift and cut the corner

Choose unitary matrix lifts `U_n(g)` on an increasing sequence of finite
subsets of `G`.  Their pointwise multiplication defects tend to zero in
operator norm.  Evaluate the finite average `(NAC1)` to obtain matrices
`q_n`.  The identities

```text
q_K^*=q_K,       q_K^2=q_K,       [q_K,g]=0                  (NAC6)
```

hold in `C[G]`, so their evaluations have operator-norm defects tending to
zero.  After replacing `q_n` by its self-adjoint part, functional calculus
at `1/2` gives projections

```text
p_n=1_[1/2,infinity)(q_n),       ||p_n-q_n|| -> 0.           (NAC7)
```

Because `||theta(q_K)||=1`, pass to a subsequence on which `p_n` is nonzero.
The last identity in `(NAC6)` and the spectral gap in `(NAC7)` give

```text
||[p_n,U_n(g)]|| -> 0                                               (NAC8)
```

for every fixed `g`.  Put `r_n=rank(p_n)` and identify
`p_n M_(d_n) p_n` with `M_(r_n)`.  No positive lower bound on `r_n/d_n` is
asserted or needed.

## The algebraic corner produces a CE trace

Let `y_1,...,y_s` be bounded generators of `B` and write the finite group-ring
elements

```text
a_j=Phi(y_j) in q_K C[G] q_K.                                (NAC9)
```

Evaluate their finite word supports at the `U_n` and compress:

```text
A_(j,n)=p_n a_j(U_n) p_n in M_(r_n).                         (NAC10)
```

Every defining star-polynomial identity of `B`, every corner identity
`q_K a_j q_K=a_j`, and every equality between the finitely many group-ring
coefficients in `(NAC9)` is a finite algebraic consequence of group word
equalities.  Pointwise operator-norm multiplicativity, `(NAC7)`, and
`(NAC8)` therefore imply

```text
||f(A_(1,n),...,A_(s,n))|| -> 0                              (NAC11)
```

for every defining relation `f` of `B`; the image of `1_B` tends to the
corner identity `p_n`.  Uniform boundedness follows from the fixed finite
group-ring supports.

Pass to a free ultrafilter.  The classes of the `A_(j,n)` define a unital
star homomorphism from `B` into the tracial matrix ultraproduct built from

```text
(M_(r_n), tr_(r_n)).                                        (NAC12)
```

Indeed operator-norm convergence in `(NAC11)` implies normalized
Hilbert--Schmidt convergence after the corner has been normalized by
`r_n`.  Pulling back the ultraproduct trace gives a Connes-embeddable tracial
state on `B`.  This contradicts the hypothesis on `B`.

Therefore every `theta` as in `(NAC3)` satisfies

```text
theta(q_K)=0,          theta(e_K)=1.                       (NAC13)
```

Write `u_k=theta(k)`.  Since their average is one,

```text
sum_(k in K) (1-u_k)^*(1-u_k)
 =2|K|1-sum_k u_k-sum_k u_k^*=0.                          (NAC14)
```

Every summand is positive, so each is zero and `u_k=1` for every `k in K`.
The original `theta` was arbitrary, hence `K<=Rad_MF(G)`.  Since `K` is
nontrivial, the MF radical of `G` is nontrivial and `G` is weak non-MF.

This also explains why one selected irreducible block is insufficient.  A
corona representation may annihilate that block while retaining another
nontrivial type, but annihilating the sum of all nontrivial types forces the
entire finite subgroup to become trivial.  Every operation used above is
finite-group averaging, operator-norm functional calculus, projection
compression, or intrinsic matrix-corner trace normalization.  End proof.
