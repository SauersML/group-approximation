---
rg: 2
id: atomic-three-row-prototype-gap-equivalence-proof
kind: route
title: Apply the atomic corner inequality and reverse it with the zero tuple
target: atomic-three-row-compiler-is-prototype-gap-equivalent
requires:
  - atomic-leavitt-gap-on-nonzero-matrix-corner
---

Assume `(ATG1)` and abbreviate its three left-hand sides by
`d_0,d_1,d_sum`.  The binary case of the atomic corner inequality gives

```text
1<=d_0+d_1+d_sum.
```

Each term is at most `C epsilon(U)`, hence

```text
1<=3C epsilon(U),
```

which is `(ATG2)` with `gamma=1/(3C)`.

Conversely, assume `(ATG2)` and put

```text
s_0=s_1=t_0=t_1=0 in p_U M_d(C) p_U.
```

Because `p_U` is a nonzero projection, all three defects in `(ATG1)` are
exactly

```text
||-p_U||_op=1.
```

But `1<=epsilon(U)/gamma`, so `(ATG1)` holds with `C=1/gamma`.

Finally, write each fixed null word `q_j` as a product of `A_j` conjugates
of defining relators and their inverses.  A unitary telescoping estimate
gives

```text
||q_j(U)-1||_op<=A_j Def_R(U).
```

Taking `A=max_j A_j` proves `(ATG3)`, and combining `(ATG2)` with `(ATG3)`
proves `(ATG4)`.  In the reverse direction the defining relators form a
finite prototype list and their maximum discrepancy is `Def_R(U)`, so a
direct marked-sector presentation gap is an instance of `(ATG2)`.

For the final equivalence, failure of `(ATG4)` supplies tuples `U_n` with
`Def_R(U_n)->0` and nonzero rounded involution atoms.  After discarding a
finite prefix, rounding error is below one, so
`||w(U_n)-1||_op>=1`.  Coordinatewise evaluation therefore defines a
homomorphism to a norm matrix corona whose value at `w` is not one.

In the other direction, lift the finitely many generator values of a corona
homomorphism to unitary matrix sequences.  Every defining relator evaluates
to one in the quotient, so their coordinate defects tend to zero.  If the
image of the involution `w` is nontrivial, its distance from one is two.
Rounding its coordinate lifts to involutions therefore gives a nonzero
nontrivial spectral atom along infinitely many coordinates.  This violates
`(ATG4)`.  Thus `(ATG4)` is equivalent to killing `w` in every such corona;
normal generation makes that equivalent to killing every group element.
