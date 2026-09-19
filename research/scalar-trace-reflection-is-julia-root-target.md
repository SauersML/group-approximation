---
rg: 2
id: scalar-trace-reflection-is-julia-root-target
kind: claim
title: Scalar trace reflection is the exact remaining Julia root target
distinct_from:
  one-additive-commutator-suffices-for-julia-return: that asks a compiler to output complex matrices realizing one small additive-commutator residual; this removes those matrices and retains only the scalar inequality which is quantitatively equivalent for the downstream endpoint.
  cyclic-acceptance-root-needs-kernel-reflection: that asks a root defect to upper-bound the HS norm of a positive coefficient; this asks only for its normalized trace and is strictly weaker than coefficient-norm reflection.
  char-p-weyl-blocks-local-commutator-decoder: that refutes scalar reflection from the paired finite root packet alone; this identifies scalar reflection as the minimal positive theorem the full finite-coordinate presentation must supply.
---

ESTABLISHED.  Let `P in M_d(C)` be a projection, let `A=A^*` be a positive
contraction, and put `C=P-A`.  The exact semantic content of a decoded
additive-commutator residual is

```text
inf_(X,Y in M_d(C)) ||[Y,X]-C||_2=|tr_d(C)|.            (SJR1)
```

Moreover the infimum is attained with `Y` unitary and `||X||<=2`, uniformly
in `d`.  Consequently, after a finite-coordinate compiler has selected the
depth `t`, it is unnecessary to decode either coefficient matrix `X_t,Y_t`
or the products `Y_tX_t,X_tY_t`.  It is enough to prove directly from its
selected root word `r_t` that

```text
|tr_d(P)-tr_d(A_t)|
 <= Omega(||r_t(U)-I||_2+Def(U)),                      (SJR2)
```

for one modulus `Omega(s)->0` independent of matrix dimension and selected
depth.  Since `r_t` is a relator output of the activated branch, its defect
tends to zero, and the Fanizza heat estimate gives

```text
tr_d(P)<=Omega(o(1))+C_m/(4t^2).                       (SJR3)
```

Thus `(SJR2)` is sufficient for exactly the same mark collapse as a decoded
residual.

It is also quantitatively necessary at the semantic level.  If matrices
`X_t,Y_t` satisfy

```text
||[Y_t,X_t]-(P-A_t)||_2<=epsilon,                       (SJR4)
```

then trace cyclicity gives `(SJR2)` with right side `epsilon`.  Conversely,
if the left side of `(SJR2)` is `epsilon`, the bounded self-adjoint
commutator normal form realizes `(SJR4)` with residual exactly `epsilon`.
The converse matrices need not be group-word definable; their role is only
to prove that scalar reflection loses no semantic strength.

Therefore the final root groupification problem is strictly smaller than a
coefficient decoder.  Its minimal positive statement is a **matrix-only
scalar reflection law** for the one activated root comparison.  It requires
no approximate ring representation, no full coefficient HS norm, and no
authenticated multiplication table.

The word “matrix-only” remains load-bearing.  The law cannot be tracially
functorial by the regular firewall, and
`char-p-weyl-blocks-local-commutator-decoder` shows that even exact paired
Steinberg triangles plus canonical finite-packet trace do not imply it.  A
successful proof must couple the activated root to a finite-coordinate
multiplicity/rank invariant which excludes the characteristic-`p` Weyl cell.
