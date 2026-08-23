---
rg: 2
id: affine-frobenius-hecke-crt-shared-involution-interpolation
kind: claim
title: Interpolate each shared BCS involution across the large affine Frobenius right ideals
distinct_from:
  affine-frobenius-packets-solve-local-row-mask-storage: that produces the fixed context PVMs and their local marginals; this must construct one global group-algebra involution agreeing with all occurrences on private masks.
  signed-hecke-block-escaping-cycle-holonomy: that closes exact marginal equality in one common signed corner; this asks only rowwise right-ideal agreement with a weighted deficit budget.
  free-relative-placement-closes-one-balanced-chord: that may choose a new joint coordinate placement for one edge; this cannot change the already fixed context PVM or use a separate shared involution on each edge.
---

OPEN.  Starting with the affine Frobenius context packets of
`affine-frobenius-packets-solve-local-row-mask-storage`, enlarge their free
product by finitely many group elements and finite-support Hecke coefficients
so that for every variable `x` there is one element

```text
B_x=B_x^*=B_x^(-1)                                    (AFI1)
```

and, for every incident context, a projection `q_(c,x)` with

```text
(B_x-A_(c,x))q_(c,x)=0.                               (AFI2)
```

The same fixed context PVM supplies all `A_(c,x)`, and the weighted sum of
canonical deficits of the masks, together with predicate deficits, is below
the finite game gap.

For the explicit Fourier masks one may take

```text
d_c=(1/p)sum_(j=0)^(p-1)u_c^j,       e_c=1-d_c,
q_(c,x)=e_c.                                           (AFI3)
```

Over `K=Q(zeta_p)`, the incidence equation is then exactly

```text
(B_x-A_(c,x))e_c=0
 iff B_x-A_(c,x) in K[Gamma]d_c.                       (AFI4)
```

Thus for `x` occurring in `c_1,...,c_m` the unresolved simultaneous problem
is the literal noncommutative affine CRT

```text
B_x in intersection_i(A_(c_i,x)+K[Gamma]d_(c_i)),
B_x^*=B_x,       B_x^2=1.                              (AFI5)
```

In particular every pair must satisfy

```text
A_(c,x)-A_(d,x) in K[Gamma]d_c+K[Gamma]d_d.            (AFI6)
```

The final presentation must also preserve the embeddings of every packet
`H_c`.  Free-product normal form proves those embeddings before the
interpolation relations are imposed; it gives no injectivity theorem after
the quotient.  Both nonemptiness of `(AFI5)` and packet injectivity are
load-bearing parts of this open claim.

## Attempts

- A literal group element cannot implement arbitrary matrices on the whole
  faithful Frobenius block; `finite-support-one-sided-stabilizers-are-torsion`
  gives the general support obstruction.  More sharply,
  `literal-involution-agreement-mass-at-most-half`
  shows that one distinct literal involution already spends deficit at least
  `1/2`.  The shared `B_x` must be a genuinely additive group-algebra unitary.
- For the Fourier mask the support obstruction is exact.  If
  `H_c<=Gamma`, `A in K[H_c]`, and `b notin H_c`, then `Ae_c` is supported
  in `H_c`, while `be_c` is supported in the disjoint coset `bH_c`; neither
  is zero, so `(A-b)e_c!=0`.  More generally decompose
  `K[Gamma]=directsum_r rK[H_c]` over left cosets.  Right multiplication by
  `e_c` preserves each summand.  If `Be_c=Ae_c`, every off-packet component
  obeys `B_r e_c=0`, equivalently `B_r=B_r d_c`.  Every discrepancy is
  therefore confined to the small trivial block; adjoining a stable-letter
  involution does not solve `(AFI5)`.
- Direct orthogonal patching spends total trace at least one.  A common mask
  recreates the stronger signed-corner problem.  The intended room is a
  multi-piece self-adjoint Hecke unitary on several noncommuting large right
  ideals.
- The context blocks cannot remain freely independent while that unitary is
  added.  `rowwise-shared-involution-forces-pairwise-marginal-closeness`
  gives the necessary inequality
  `(1/4)||A_(c,x)-A_(d,x)||_2^2<=delta_(c,x)+delta_(d,x)`.
  For unbiased marginals in distinct free factors the left side is `1/2`.
  The overlap relations must therefore create the required canonical
  correlation among the fixed marginals, not merely attach `B_x` afterward.
- Independent uses of the one-chord transport cell may change the context
  PVM from incidence to incidence.  Such a construction does not feed the
  ambient identity-Gram BCS gap and is invalid.
- A finite graph of finite groups remains virtually free and therefore
  cannot realize a strict row-mask budget.  At least one overlap cycle must
  use a non-Bass--Serre relation or infinite edge algebra.
- This remains true even for coefficient-valued finite bridge packets.
  Residual finiteness supplies a finite quotient injective on the finite set
  of support differences needed to preserve all displayed group-algebra
  identities and their identity coefficients.  Its finite regular
  representation would reproduce the same strict deficit certificate,
  contradicting the fixed finite-dimensional BCS gap.  Hence the global
  interpolation relations themselves must leave the finite Bass--Serre
  class.
- `shared-involution-right-ideal-interpolation-criterion` gives the complete
  operator answer.  The several prescriptions are compatible exactly when
  the two row Gram identities `(SIC4)` hold.  In a finite von Neumann algebra
  their sum/difference columns always produce a reflecting involution.
  Finite support is strictly stronger: it is equivalent to one algebraic
  projection `p_x` satisfying `p_xq_i=((1-A_i)/2)q_i` for every incidence.
  Julia or matrix dilation only stabilizes this projection CRT, and compressed
  agreement is equivalent to full agreement for the reducing Frobenius
  masks.  The remaining algebraic target is isolated as
  `affine-frobenius-algebraic-projection-crt`.
