---
rg: 2
id: choi-diagonal-annihilation-equalizes-not-softens
kind: claim
title: Unit-zero Choi annihilation equalizes diagonal relator-square moments but cannot make them soft
distinct_from:
  positive-packet-witness-gap-endpoint: that gives an abstract two-outcome positivity counterexample and the exact gap-compactness dichotomy; this computes the matrix-unit consequences of annihilating a square-enlarged native reservoir and gives a fixed-gap counterexample inside an actual finite-dimensional packet of the triangle relator ideal.
  native-relator-soft-modes-persist-in-simple-ideal-blocks: that proves low-energy vectors exist in irreducible full-ideal packets independently of Choi infeasibility; this shows the diagonal vectors selected by a positive affine witness need not be any of those soft vectors.
  ideal-block-infeasibility-has-positive-reservoir-witness: that constructs the positive witness for an actual failed affine packet slice; this proves that positivity and annihilation, even together with all matrix-unit and square-moment identities they imply, do not by themselves correlate its diagonal densities with the soft spectrum.
  cross-face-choi-annihilation-is-scalar-partition: that computes the exact identity obtained when only the sum of three positive face components annihilates the reservoir and gives a common-edge hard-energy realization; this treats the stronger facewise-annihilating diagonal special case.
---

**ESTABLISHED (exact diagonal identity and native-packet no-go).**  Let `B`
be a finite-dimensional unital C-star algebra, let `rho:A->M_d` be a
finite-dimensional representation, let `L subset A` be a finite-dimensional
self-adjoint space, and let `Omega_B` be a positive Choi functional on maps
`B->M_d` satisfying

```text
Omega_B(rho o v)=0
for every v in L_sa(B,L) with v(1)=0.                    (DCA1)
```

Write `B=direct_sum_r M_(n_r)` and use matrix units `e_ij^r`.  Under the
Choi identification, write the positive functional as `omega` on
`direct_sum_r M_(n_r)(M_d)` and define its diagonal output functionals

```text
lambda_(r,i)(a)=omega(e_ii^r tensor a),       a in M_d.   (DCA2)
```

Then for every `ell in L` and every two diagonal coordinates `(r,i),(s,j)`,

```text
lambda_(r,i)(rho(ell))=lambda_(s,j)(rho(ell)).             (DCA3)
```

The off-diagonal coefficient functionals of `omega` vanish on `rho(L)`.
Consequently, if the reservoir has been enlarged by `x^*x` for some
`x in A`, then

```text
lambda_(r,i)(rho(x)^*rho(x))
 =lambda_(s,j)(rho(x)^*rho(x)) >=0.                       (DCA4)
```

If `lambda_(r,i)(a)=Tr(D_(r,i) a)` for the diagonal Choi density
`D_(r,i)>=0`, `(DCA4)` says exactly that the `D_(r,i)`-weighted relator
energies are equal.  It supplies neither an upper bound nor vanishing of
their common value.

This limitation persists with a fixed affine separation gap in an actual
finite-dimensional packet of the native Kac--Moody triangle ideal.  There
are

```text
A=C^*(G_0),       I=ker(A->>C^*(Lambda)),
E=S_Delta=C^*(P_12)+C^*(P_23)+C^*(P_13),
rho:A->M_d irreducible,       d>=2,       rho(I)=M_d,
y=y^* in the algebraic native relator ideal,
rho(y)=I_d,
L=span_C{y,y^2} subset I,       rho(L)=C I_d,              (DCA5)
```

a unital self-adjoint linear quotient section `t:E->A`, and a positive Choi
functional `Omega` such that the relative-unital affine slice

```text
[rho o t + rho_* L_sa(E,L)] intersect UCP(E,M_d)           (DCA6)
```

is empty, while

```text
Omega(rho o v)=0                         if v(1)=0,
Omega(rho o t)-sup_(theta in UCP(E,M_d))Omega(theta)=2.    (DCA7)
```

Nevertheless the two diagonal Choi density vectors which witness `(DCA7)`
both have maximal `y`-energy:

```text
||rho(y)xi||^2=||rho(y)eta||^2=1.                          (DCA8)
```

Thus closing a native reservoir under finitely many products `x^*x` can
transfer a relator moment from one diagonal density to every other diagonal
density, but cannot create a low-energy density.  The failed implication is
already compatible with the actual triangle operator system, an actual RFD
packet, the actual relator ideal, a legitimate quotient section, positivity,
unit-zero annihilation, and a nondegenerate affine gap.

This is already the **optimistic** facewise situation.  The positive witness
in `ideal-block-infeasibility-has-positive-reservoir-witness` is a sum of
three positive face Choi functionals, whereas its annihilation conclusion is
for the sum.  Cancellation between faces need not make any one face component
satisfy `(DCA1)`.  Hence the global three-face witness generally gives less,
not more, than the equal-moment identity proved here.

**Exact scope.**  The section in the counterexample is chosen using the
packet.  Therefore this does not decide feasibility for one particular
preselected section and an exhausting sequence of reservoirs.  It proves
that the desired soft-vector extraction cannot be a formal consequence of
finite-face Choi positivity, matrix-unit decomposition, native-ideal support,
square closure, and `(DCA1)`.  A successful triangle theorem must use an
additional identity involving the specific preselected lift across two or
more faces; diagonal square moments alone have the wrong sign of information.

Proof: `matrix-unit-choi-diagonal-gauge-counterexample-proof`.

DERIVATION
matrix-unit-choi-diagonal-gauge-counterexample-proof
