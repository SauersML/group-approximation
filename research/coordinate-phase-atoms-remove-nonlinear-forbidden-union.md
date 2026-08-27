---
rg: 2
id: coordinate-phase-atoms-remove-nonlinear-forbidden-union
kind: claim
title: Coordinate phase words reduce a nonlinear forbidden union to finitely many assignment atoms
distinct_from:
  phase-covariance-words-exactly-measure-type-transport-leakage: that treats an abstract type PVM once word-spectral phase tags are supplied; this uses the original BCS coordinate involutions themselves and performs the forbidden-carrier trimming atom by atom.
  forbidden-weighted-type-carrier-coverage-is-rank-rounding: that trims one aggregate forbidden/type intersection and may leave a noncanonical within-type cut; this refines the trimming to the literal joint eigenspaces of the context coordinates.
  finite-phase-tags-authenticate-forbidden-cuts: that asks for the remaining within-atom actuator estimate; this proves that neither the nonlinear union nor cross-assignment leakage belongs to that remaining gate.
---

Let `Z_1,...,Z_k` be commuting involutions and, for
`a in {+1,-1}^k`, put

```text
P_a=product_i (I+a_i Z_i)/2.                           (CPA1)
```

The `P_a` form a PVM.  For a fixed forbidden set `R`, its projection is

```text
F_R=sum_(a in R)P_a.                                  (CPA2)
```

Let `(Q_lambda)` be a finite family of type projections commuting with all
the `Z_i`.  For every `(a,lambda)` choose a subprojection

```text
C_(a,lambda)<=P_a Q_lambda
```

whose rank is the largest multiple of four not exceeding
`rank(P_aQ_lambda)`.  Then

```text
sum_(a in R,lambda) tr(C_(a,lambda))
 >=tr(F_R sum_lambda Q_lambda)-3|R||Lambda|/d.          (CPA3)
```

Thus the marked forbidden mass can be covered, up to `o(1)`, by carriers
each lying in one literal assignment atom.  No spectral word for the
nonlinear characteristic function `1_R` is required.

The same coordinate words control every cross-assignment transport.  If
`W_1,...,W_k` is a second commuting involution tuple with atoms `Q_b` and
`U` is unitary, then the exact identity

```text
sum_i ||Z_i U-U W_i||_2^2
 =4 sum_(a,b) Ham(a,b)||P_a U Q_b||_2^2               (CPA4)
```

holds, where `Ham` is Hamming distance.  Indeed, insert the two joint PVMs
on either side of each summand; on `P_a U Q_b` the coefficient is
`a_i-b_i`, and orthogonality removes all cross terms.  In particular,

```text
sum_(b!=a)||P_a UQ_b||_2^2
 <=(1/4)sum_i||Z_iU-UW_i||_2^2.                        (CPA5)
```

Every term on the right is the defect of the ordinary covariance word
`Z_i U W_i^(-1)U^(-1)`.  After fixed-packet exactification, the same formula
has only the existing vanishing correction.

Consequently the nonlinear predicate contributes only a finite external
sum over forbidden assignments.  Once type and coordinate phases have been
matched, the unresolved selector problem lies entirely inside one fixed
joint eigenspace `P_aQ_lambda`, where all original BCS coordinate words are
scalar.  Phase coding cannot see that remaining multiplicity fiber.

