---
rg: 2
id: cross-face-choi-annihilation-is-scalar-partition
kind: claim
title: Cross-face Choi annihilation is exactly a positive scalar partition of the common unit
distinct_from:
  choi-diagonal-annihilation-equalizes-not-softens: that computes the diagonal and off-diagonal identities when one positive face Choi functional annihilates the reservoir by itself; this computes the exact identity left when only the sum of the three positive face components annihilates it and tests the identity on a projection in the shared tree edge.
  ideal-block-infeasibility-has-positive-reservoir-witness: that constructs three positive face components whose sum is a dimension-uniform affine witness; this determines all rank-one cross-face consequences of their global unit-zero annihilation and shows they do not select a soft relator density.
  scalar-tree-perturbations-linearly-control-closing-face: that transfers primal cb-norm motion between compatible face restrictions; this is a dual Choi-marginal identity and a fixed-gap counterexample, with no assumption that the primal map is close to the scalar face.
---

**ESTABLISHED (exact cross-face identity and shared-edge no-go).**  Let

```text
E=B_12+B_23+B_13                                             (CFA1)
```

be a finite-dimensional operator-system sum of unital finite-dimensional
C-star algebras with their units identified.  Let `rho:A->M_d`, let
`L subset A` be self-adjoint, and suppose

```text
Omega(phi)=sum_H Omega_H(phi|_(B_H)),
Omega_H(alpha)>=0 for every cp alpha:B_H->M_d,
Omega(rho o v)=0 for every v in L_sa(E,L), v(1)=0.          (CFA2)
```

For `a in rho(L)` define the **input marginal** `K_H(a) in B_H` by

```text
f(K_H(a))
 =Omega_H(b |-> f(b)a),       f in B_H^*.                  (CFA3)
```

Then there is a scalar `c_a` such that

```text
sum_H K_H(a)=c_a 1_E.                                      (CFA4)
```

For a basis of `rho(L)` these identities are also sufficient for
annihilation of every unit-zero finite-rank correction.  Thus `(CFA4)`, with
one scalar for each represented reservoir coefficient, is not merely a
necessary trace shadow: it is the complete rank-one linear content of the
last clause of `(CFA2)`.

This sum is taken in the concrete operator system `E`, so `(CFA4)` already
includes every shared-edge and common-unit identification.  If `a>=0`, then

```text
K_H(a)>=0 for every H,       c_a>=0.                        (CFA5)
```

In particular, after adjoining `x^*x` to the native reservoir,

```text
sum_H K_H(rho(x)^*rho(x))=c_x 1_E,       K_H>=0.            (CFA6)
```

Thus the complete rank-one consequence of global annihilation is a positive
partition of a scalar common-unit mass.  Neither compatibility nor positivity
forces `c_x`, or any nonzero summand in `(CFA6)`, to be small.

The obstruction is realized inside the actual `(3,3,4)` Kac--Moody triangle,
with the **same preselected quotient section on all three faces** and with a
test projection in their shared tree edge.  There are

```text
A=C^*(G_0),       I=ker(A->>C^*(Lambda)),
E=S_Delta=B_12+B_23+B_13,
rho:A->M_d irreducible,       rho(I)=M_d,       d>=2,
y=y^* in the algebraic native ideal,       rho(y)=I_d,
L=span_C{y,y^2},
p a nontrivial projection in C^*(P_2) subset B_12 cap B_23, (CFA7)
```

one unital self-adjoint quotient section `t:E->A`, and three nonzero positive
face Choi functionals `Omega_12,Omega_23,Omega_13` satisfying `(CFA2)`.  Their
sum has the fixed affine gap

```text
Omega(rho o t)-sup_(theta in UCP(E,M_d))Omega(theta)=4,     (CFA8)
```

while the corresponding affine slice is empty.  All shared-edge and unit
values of `rho o t` agree exactly because they are restrictions of that one
global map.  For the square `y^2`, the three input marginals are

```text
K_12(I_d)=K_23(I_d)=K_13(I_d)=1,
sum_H K_H(I_d)=3 1_E.                                      (CFA9)
```

Every vector occurring in every face density has `y`-energy one.  Hence even
the most symmetric hard-energy scalar partition satisfies all cross-face
identities, exact shared-edge compatibility, positivity, annihilation, and a
dimension-free affine gap.

**Exact scope.**  As in the one-face counterexample, the section is selected
before the three Choi components but after choosing the packet.  This does
not decide an exhausting sequence for a section chosen independently of all
packets.  It proves that no dimension-free soft-vector conclusion follows
from shared-edge/unit compatibility and the positive face Choi decomposition
alone.  A live theorem must use how one externally fixed lift varies across
an exhausting family of representations, not another finite-packet
cross-face marginal identity.

Proof: `derive-choi-input-marginals-and-share-one-hard-edge`.

DERIVATION
derive-choi-input-marginals-and-share-one-hard-edge
