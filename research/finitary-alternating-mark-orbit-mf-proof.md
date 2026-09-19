---
rg: 2
id: finitary-alternating-mark-orbit-mf-proof
kind: route
title: Put disjoint double transpositions in the natural permutation norm corona
target: infinite-orthogonal-mark-orbit-is-mf-compatible
requires:
  - atomic-leavitt-gap-on-nonzero-matrix-corner
---

Every finite subset of `A_fin` is contained in one finite alternating group.
Thus `A_fin` is locally finite, hence LEF and operator-MF.

For completeness, `A_fin` is simple.  If `1!=g` lies in a normal subgroup
`N normal A_fin`, choose `m>=5` containing the support of `g`.  Then
`N intersect A_m` is a nontrivial normal subgroup of the simple finite group
`A_m`, so it is `A_m`.  For every `r>=m`, the same argument applied to
`N intersect A_r`, which already contains `A_m`, gives `A_r<=N`.  Hence
`N=A_fin`.  Since `w` is nontrivial, its normal closure is therefore the
whole group.

Define the coordinate permutation matrices as follows.  For `g in A_fin`,
let `pi_n(g)` be its natural permutation matrix on `C^n` once the support of
`g` is contained in `{1,...,n}`, and put `pi_n(g)=I_n` at the finitely many
earlier coordinates.  For every fixed `g,h`, the equality

```text
pi_n(gh)=pi_n(g)pi_n(h)
```

holds for all sufficiently large `n`.  Therefore

```text
rho(g)=[(pi_n(g))_n]
```

defines the homomorphism `(IOM1)`.  If `g!=1`, its eventual permutation
matrix has a nontrivial root of unity as an eigenvalue, so

```text
limsup_n ||pi_n(g)-I_n||_op>0.
```

Thus `rho` is faithful.

Partition the positive integers into four-point blocks

```text
B_k={4k+1,4k+2,4k+3,4k+4},
```

and let `w_k` be the product of the two adjacent transpositions in `B_k`.
Every `w_k` has cycle type `(2,2)`, hence is conjugate to `w=w_0` in
`A_fin`.  One can see the parity directly: start with any finitary
permutation carrying the two pairs of `B_0` to those of `B_k`; if it is odd,
multiply it by either transposition in `B_k`, which is odd and centralizes
`w_k`.  The resulting even permutation `h_k` still satisfies

```text
h_k w h_k^(-1)=w_k.                                      (IOM4)
```

Put

```text
p_k=(1-rho(w_k))/2=rho(h_k)p rho(h_k)^(-1).               (IOM5)
```

At every sufficiently large coordinate the `-1` eigenspace of `pi_n(w_k)`
is spanned by the two difference vectors belonging to the two transpositions
in `B_k`.  It has dimension two.  Difference vectors belonging to distinct
blocks have disjoint supports, so

```text
p_j p_k=0                         whenever j!=k.           (IOM6)
```

Here `(IOM6)` holds coordinatewise after finitely many initial coordinates,
which is exactly equality in the norm corona.  Equations `(IOM4)--(IOM6)`
give infinitely many pairwise orthogonal conjugates of the nonzero marked
projection `p`.

Finally, `rho(w)!=1` by faithfulness, so `w` does not belong to the MF
radical.  More explicitly, each coordinate corner representing `p` is
eventually `M_2(C)`.  If four corner operators had the two binary inverse
defects and the completeness defect tending to zero, the Atomic Leavitt Gap
would give at every sufficiently large coordinate

```text
1 <= ||t_0s_0-p||_op+||t_1s_1-p||_op
     +||s_0t_0+s_1t_1-p||_op,
```

contradicting convergence of all three terms to zero.  Hence the orthogonal
orbit supplies only ambient packing and cannot manufacture an atomic Morita
return to its source projection.
