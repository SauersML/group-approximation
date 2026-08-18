---
rg: 2
id: printed-ultraproduct-ambient-for-kazhdan-transport-proof
kind: route
title: The Hilbert ultraproduct carries the norm-ultraproduct action faithfully
target: printed-ultraproduct-ambient-for-kazhdan-transport
requires: []
artifacts:
  - non_mf_groups_exist.tex
  - GroupApproximation/Sofic/UltraproductAdjointAmbient.lean
  - GroupApproximation/Sofic/UltraproductModelConstructionAssembly.lean
  - GroupApproximation/Sofic/ManuscriptKazhdanTransport.lean
---

# Direct construction of KT.02--KT.04

Fix a free ultrafilter `omega` and Hilbert spaces
`K_n=L^2(M_(d_n)(C),tr_(d_n))`.  Everything the printed proof asks for is a
standard Banach/Hilbert ultraproduct construction; no operator-algebraic
existence theorem is needed.

## 1. The Hilbert-space ultraproduct

Let

```text
ell_infty(K_n) = { xi=(xi_n) : sup_n ||xi_n|| < infinity }
N_omega        = { xi : lim_omega ||xi_n|| = 0 }.
```

`N_omega` is a closed linear subspace.  Put

```text
K_omega = ell_infty(K_n) / N_omega,
< [xi_n], [eta_n] > = lim_omega <xi_n,eta_n>.
```

The scalar ultralimit exists because the inner-product sequence is bounded.
Cauchy--Schwarz shows the formula is independent of representatives and
positive definite modulo `N_omega`; in particular

```text
||[xi_n]|| = lim_omega ||xi_n||,
[xi_n]=[eta_n]  <=>  lim_omega ||xi_n-eta_n||=0.                 (KT.02)
```

Completeness is automatic: `ell_infty(K_n)` is a Banach space and
`N_omega` is closed, hence the quotient is Banach.  The displayed inner
product induces its quotient norm (equivalently the parallelogram law passes
to the quotient), so the Banach quotient is a Hilbert space.

## 2. Coordinate operators descend

For a uniformly bounded family `T=(T_n)` with `T_n in B(K_n)`, define

```text
rho(T)[xi_n] = [T_n xi_n].
```

If `[xi_n]=0`, then

```text
||T_n xi_n|| <= (sup_n ||T_n||) ||xi_n|| ->_omega 0,
```

so the action is well-defined.  It is plainly linear, multiplicative,
*-preserving and unital, and

```text
||rho(T)|| <= lim_omega ||T_n||.
```

If `||T_n|| ->_omega 0`, the induced operator is zero.  Hence `rho` factors
through the norm ultraproduct

```text
B_omega = prod_omega B(K_n).
```

This gives the multiplicative action required in KT.03/KT.04.

## 3. The action is faithful (indeed isometric)

Let `a=[T_n] in B_omega` and write
`c=lim_omega ||T_n||`, the quotient norm.  For each `n` choose a unit vector
`xi_n` with

```text
||T_n xi_n|| >= ||T_n|| - 1/n
```

(exact norm-attainment is available here because every `K_n` is finite
dimensional, but an approximate maximizer would suffice).  Then
`xi=[xi_n]` is a unit vector in `K_omega` and

```text
||rho(a) xi|| = lim_omega ||T_n xi_n|| = c.
```

Thus `||rho(a)||>=c`; together with the previous inequality,
`||rho(a)||=c`.  So `rho` is isometric and in particular faithful.

Consequently algebraic identities read from the Hilbert-space action descend
back to `B_omega`.  In particular, for projections `P,Q`, range inclusion
`Ran(P) subset Ran(Q)` is equivalent on a Hilbert space to `QP=P`; taking
adjoints also gives `PQ=P`.  Faithfulness turns those operator identities
into the identities in `B_omega` used by the printed absorption argument.
This is exactly the KT.04 read-back demanded by the claim.

## 4. Match to the matrix adjoint model

For the manuscript's coordinates, `Ad(U_n)` acts unitarily on `K_n` because
left and right multiplication by a unitary preserve normalized
Hilbert--Schmidt norm.  Hence the already-defined coordinate family
`Ad(U_n(g))` gives an element of `B_omega`, and its action under `rho` is
literally

```text
[x_n] |-> [U_n(g) x_n U_n(g)^*].
```

Operator-norm asymptotic multiplicativity of the `U_n` makes these classes a
genuine representation in the ultraproduct, exactly as in the repository's
KT.01/KT.05 calculations.

Therefore the ambient package whose existence was left open in the printed
route exists for every free ultrafilter.  This establishes
[[printed-ultraproduct-ambient-for-kazhdan-transport]].  It does not replace
the repository's finite-stage proof of Kazhdan transport; it repairs the
separate ultraproduct proof printed in the manuscript.

## Machine-checked form

The argument above is also formalized, so this route is not carried by its
prose alone.  `UltraproductModelConstruction.nonempty_ultraproductAdjointModel`
(`Sofic/UltraproductModelConstructionAssembly.lean`) returns a term of
`UltraproductAdjointModel iota s d U omega` for every `omega` below the
cofinite filter, taking as input exactly what the transport theorem already
assumes: property (T) of `Gamma`, `s iota(Gamma) s^-1 <= iota(Gamma)`,
`0 < d n`, and operator-norm asymptotic multiplicativity of `U`.  Sections 1--3
above correspond to the `Vec`/`act` construction and its multiplicativity,
unitality and faithfulness lemmas; section 4 to the `compressionRep` bundling of
the coordinate adjoint family.  `manuscriptKazhdanTransport`
(`Sofic/ManuscriptKazhdanTransport.lean`) then states the manuscript's
`thm:kazhdan-transport` with no ambient hypothesis and discharges it with that
constructor.  Both modules are in the root import closure, so they are covered
by `lake build` and the kernel audit.
