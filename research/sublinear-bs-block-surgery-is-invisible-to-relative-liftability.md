---
rg: 2
id: sublinear-bs-block-surgery-is-invisible-to-relative-liftability
kind: claim
title: Sublinear BS block surgery does not change the relative ultraproduct lifting class
distinct_from:
  invariant-bs-block-cut-leaves-a-passive-coordinate-basin: that proposes deleting the active invariant hull and proving a coordinate basin on the passive block; this proves the deletion cannot itself improve the remaining liftability problem.
  authenticated-core-union-basin-is-relative-liftability: that identifies the endpoint-union basin with relative liftability for a supplied authenticated sequence; this proves invariance of that property under the particular sublinear block compression, polarization, and endpoint replacement used by the BS14 active/passive construction.
  low-rank-reflection-surgery-preserves-the-exact-bs-core: that bounds the new finite-word defects after changing a reflection on a low-rank support; this identifies the unchanged exact ultraproduct homomorphism and the unchanged flexible-lift obstruction.
---

**ESTABLISHED; ULTRAPRODUCT-ONLY PASSIVE-BASIN ARGUMENT REFUTED.**  Let
`T_n=(X_n,R_n,S_n)` be uniformly bounded tuples on `d_n` dimensions, with
`(R_n,S_n)` an exact authenticated BS core.  Let `Q_n` reduce `R_n,S_n`,
put `q_n=rank(Q_n)=o(d_n)`, and put `P_n=1-Q_n`.

Replace `X_n` by its block diagonal compression

```text
X_n^bd=Q_nX_nQ_n+P_nX_nP_n,                            (SBI1)
```

polarize the two selfadjoint compressions to reflections, and replace the
`Q_n` block by an arbitrary exact endpoint of dimension `q_n+o(d_n)`.
Call the resulting flexibly dimension-changed tuple `T_n'`.  Then

```text
dist_2^flex(T_n,T_n')->0.                              (SBI2)
```

Consequently `T_n` and `T_n'` define the same relative homomorphism

```text
Pi:PSL_2(Z[1/2])->product_omega M_(d_n)                (SBI3)
```

over the authenticated core.  In particular, `Pi` has coordinatewise
exact congruence lifts with `o(d_n)` padding if and only if the passive
block of `T_n'` does.  Thus cutting and exactly replacing the sublinear
active block cannot manufacture entry into the union of congruence
endpoint orbits.

For `(SBI2)`, the off-diagonal part of `X_n` in `(SBI1)` is supported on
`Q_n+X_nQ_n`, hence has rank at most `2q_n` and Frobenius norm at most
`2sqrt(2q_n)`.  If `A=P_nX_nP_n` and `X_n` is a reflection, then

```text
P_n-A^2=P_nX_nQ_nX_nP_n                               (SBI4)
```

is positive of rank at most `q_n`.  For a selfadjoint contraction the
nearest spectral reflection `sgn(A)` satisfies

```text
||sgn(A)-A||_F^2<=Tr(P_n-A^2)<=q_n.                    (SBI5)
```

The same estimate holds on the `Q_n` compression.  Arbitrarily changing or
padding the `Q_n` block costs at most a constant times `sqrt(q_n/d_n)` in
normalized HS.  This proves `(SBI2)`.  The passive exact core coordinates
are unchanged, while any replacement of the active core is confined to
`o(d_n)` dimensions.

Flexible liftability depends only on this relative ultraproduct class.
Indeed, if exact endpoint tuples `rho_n` on `d_n+o(d_n)` dimensions
converge to one representative, the triangle inequality with `(SBI2)`
makes them converge to the other.  Conversely the same argument reverses
the roles.  Direct-summing an arbitrary exact endpoint on the deleted
`o(d_n)` block does not affect normalized HS convergence.

The exact torsion frame does not alter this conclusion.  On the passive
block put

```text
A_n=X_nS_n^2,   B_n=X_nR_nS_n,   C_n=S_n^(-2)R_nS_n.
```

The identity `B_n=A_nC_n` is exact before torsion rounding.  If the two
cubic residuals tend to zero in operator norm, functional calculus rounds
`A_n,B_n` to exact order-three unitaries in operator norm, as in
`bs14-cubic-rounding-leaves-relative-core-basin`.  But their rounded
relative product need not equal the fixed `C_n`, nor recover one common
reflection.  In the ultraproduct all these equations were already exact;
rounding only chooses a better representative of the same `(SBI3)`.

Therefore a contradiction/ultraproduct proof of the passive coordinate
basin is circular: it obtains the exact relative homomorphism `(SBI3)`,
while coordinate basin entry is precisely a lift of that homomorphism.
The uniform tangent quotient controls distance after such a coordinate
lift has been selected and cannot select the lift.  Any completion must
add a genuinely coordinate theorem--for example relative semiprojectivity,
a uniform congruence lift, or an arithmetic reconstruction of the missing
boundary cell.  Compactness, the `o(d)` block cut, and exact torsion
localization alone do not supply it.
