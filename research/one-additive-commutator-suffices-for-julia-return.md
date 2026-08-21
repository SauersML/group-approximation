---
rg: 2
id: one-additive-commutator-suffices-for-julia-return
kind: claim
title: One additive commutator suffices for the Julia amplitude return
distinct_from:
  fanizza-heat-return-is-one-cyclic-amplitude-product: that assumes two separately decoded products approximating the marked projection and the heat amplitude; this proves that the scalar contradiction only needs their difference to be one approximate additive commutator.
  trace-cyclic-rank-mismatch-checksum: that compares the traces of two approximate products; this removes the individual product approximations and retains only one commutator residual.
  universal-block-return-violates-the-regular-firewall: that rules out a fixed tracially functorial return; this gives a smaller matrix-only semantic target and explicitly preserves the same firewall.
---

ESTABLISHED.  Fix the Fanizza heat amplitude

```text
B_t=D_R p_t(H_m),
A_t=B_t^*B_t=p_t(H_m)D_Rp_t(H_m).
```

Let `P` be a projection in a finite tracial matrix algebra and let `X,Y` be
arbitrary matrices.  The two-product payload

```text
||YX-P||_2<=epsilon,       ||XY-A_t||_2<=delta
```

implies

```text
||[Y,X]-(P-A_t)||_2<=epsilon+delta,                  (ACJ1)
```

but the latter estimate alone is already enough for the Fanizza return.
Indeed every finite-dimensional additive commutator has trace zero, so

```text
|tr(P)-tr(A_t)|
 =|tr(P-A_t-[Y,X])|
 <=||P-A_t-[Y,X]||_2.                                (ACJ2)
```

On a NONHALT instance the accelerated heat estimate gives

```text
0<=tr(A_t)=||B_t||_2^2<=||B_t||^2<=C_m/(4t^2).
```

Consequently the single semantic estimate

```text
||[Y_t,X_t]-(P-A_t)||_2<=omega(Def)                  (ACJ3)
```

implies

```text
tr(P)<=omega(Def)+C_m/(4t^2),                        (ACJ4)
```

with no bound on `||X_t||` or `||Y_t||` and no constant depending on the
matrix dimension or on `t`.  Thus the constant-sound terminal half of
`dimension-reported-julia-amplitude-return` is over-specified: for its only
downstream use, a self-indexed compiler may return one additive commutator
residual instead of authenticating `YX` and `XY` separately.

This reduction is sharp.  For every `C in M_d(C)`,

```text
inf_(X,Y in M_d(C)) ||C-[Y,X]||_2=|tr_d(C)|.          (ACJ5)
```

The lower bound follows by taking trace.  For the reverse bound write
`C=tr_d(C)I+C_0`, where `tr(C_0)=0`.  Every complex trace-zero matrix is one
additive commutator.  Here is a short proof.  Inductively choose an
orthonormal basis in which `C_0` has zero diagonal: zero belongs to the
numerical range because it belongs to the convex hull of the eigenvalues,
and after choosing a unit vector with zero diagonal entry, the compression
to its orthogonal complement again has trace zero.  In that basis choose a
diagonal matrix `D=diag(d_1,...,d_d)` with pairwise distinct entries and put

```text
Z_ij=(C_0)_ij/(d_i-d_j)  for i!=j,       Z_ii=0.
```

Then `[D,Z]=C_0`.  Taking this commutator in the infimum leaves precisely
`tr_d(C)I`, whose normalized HS norm is `|tr_d(C)|`.

Applied to `C=P-A_t`, `(ACJ5)` says that the best possible commutator
residual is exactly the scalar mismatch that the Fanizza endpoint must
force.  Thus a compiler for `(ACJ3)` is neither hiding a stronger rank
theorem nor paying for a multiplication table: semantically it is a robust
trace-zero certificate.

For the self-adjoint Fanizza target there is, moreover, no hidden
dimension-dependent norm cost.  If `C=C^*` and `tr(C)=0`, order its real
eigenvalues `lambda_1,...,lambda_d` greedily: when the current partial sum is
nonnegative choose a remaining nonpositive eigenvalue, and conversely.
Because the total sum is zero, the required sign is available until the
end, and every partial sum `s_i=sum_(j<=i) lambda_j` satisfies

```text
|s_i|<=max_j |lambda_j|<=||C||.                       (ACJ6)
```

In an eigenbasis let `S` be the cyclic shift, put
`X=S diag(s_1,...,s_d)` (with the cyclic indexing chosen so that
`s_i-s_(i-1)=lambda_i`) and `Y=S^*`.  Then

```text
[Y,X]=C,        ||Y||=1,        ||X||<=||C||.         (ACJ7)
```

For arbitrary self-adjoint `C`, apply this to
`C_0=C-tr_d(C)I`.  It realizes the exact optimum in `(ACJ5)` with `Y`
unitary and

```text
||X||<=||C_0||<=2||C||.                               (ACJ8)
```

Since `P` and `A_t` are positive contractions, `||P-A_t||<=1`; hence the
optimal Fanizza commutator residual always has factors bounded by `2` and
`1`, independent of depth and dimension.  Producing the eigenvalue ordering
and cyclic shift from group relations is still a finite-coordinate decoder
problem, but unbounded coefficient norms are not an analytic obstruction.

## Coefficient-level Steinberg compression

The smaller target has a constant-size algebraic wordization.  In any
unital ring in which the indicated elementary matrices are defined, use the
commutator convention `[g,h]=ghg^(-1)h^(-1)`.  The Steinberg relation gives

```text
[e_12(Y),e_23(X)] [e_12(X),e_23(Y)]^(-1)
   =e_13(YX-XY)=e_13([Y,X]).                          (ACJ9)
```

Therefore `(ACJ3)` is one root-coefficient comparison with
`e_13(P-A_t)`.  In the standard `3 by 3` matrix realization,

```text
||e_13(C)-e_13(D)||_(2,tr_3)=||C-D||_2/sqrt(3),       (ACJ10)
```

so this compression has a dimension- and runtime-independent constant.  It
does not require a growing Clifford multiplication table and it does not
even require two separately authenticated output coefficients.

## Exact boundary

Equations `(ACJ9)--(ACJ10)` are a coefficient-level reduction, not a missing
normalized-HS coefficient decoder for an abstract unitary representation of
a Steinberg group.  That decoder remains the load-bearing groupification
step.  Nor may `(ACJ3)` be imposed as a fixed identity valid in every finite
tracial representation: applying it at zero defect in the regular finite
von Neumann algebra for arbitrarily large `t` would force the nonzero regular
carrier `P` to have trace zero.  The stopping depth and root coefficient
comparison must still be obtained from finite matrix coordinates.  The new
conclusion is only that their terminal semantic payload is one commutator
residual, which is strictly weaker than the previously requested pair of
product residuals.
