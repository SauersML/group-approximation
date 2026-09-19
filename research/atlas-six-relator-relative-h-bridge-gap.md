---
rg: 2
id: atlas-six-relator-relative-h-bridge-gap
kind: claim
title: The six Atlas relators uniformly control the four standard H bridges
distinct_from:
  atlas-six-relator-quotient-identifies-h-bridge: that false algebraic claim asks the six relators to kill every bridge in the universal quotient; this asks only for normalized-HS control on finite regular-margin common frames and permits the bridges to survive in the Leavitt representation.
  atlas-six-relator-hyperlinear-escape-test: that identifies exact failure with a bridge-retaining hyperlinear quotient; this is the quantitative four-word inequality whose validity excludes that quotient.
  atlas-five-row-operator-phase-lift: that uses five long integral additive rows; this uses only the four literal standard-transvection bridge words and is equivalent by fixed finite-packet linear algebra.
  atlas-six-relator-regular-face-defect-floor: that removes the bridge observables entirely and asks only for a positive scalar floor on the total six-relator defect; the existing blow-up inequality makes that still sufficient for the five-row lift.
---

For every common relative chart unitary `U in U(20160k)`, prove a constant
`C_B` independent of `k` such that

```text
sum_(ell=1)^4 ||pi_U(b_ell)-1||_2^2
 <=C_B [sum_(j in {0,11,30,44,55})||pi_U(s_j)-1||_2^2
                    +||pi_U(c_19243)-1||_2^2],        (RHB1)
```

where `b_ell=i_2(t_ell)i_1(t_ell)^(-1)` and the `t_ell` are the four
standard transvections generating `H=GL_3(2)`.

By `atlas-five-row-energy-equals-h-bridge-energy`, `(RHB1)` is equivalent
to the five-row operator phase lift up to fixed constants.  It is a smaller
operator target in the presentation itself: four short group-word
displacements replace the five signed sums in `Z[A8]`.

## Attempts

- **Exact bridge filling is false.**  The canonical Leavitt quotient
  satisfies all six relators and retains every nonidentity bridge because
  the two marked `A8` charts intersect trivially.  Thus `(RHB1)` cannot come
  from van Kampen fillings or a universal tracial inequality.
- **Independent phase edges are insufficient.**  The private-edge
  countermodel kills all six multiplicative cycles while retaining additive
  circulation.  It does not satisfy the common-frame orbit identities used
  in `(RHB1)` and therefore does not refute this claim.
- **Known finite exact models do not survive the six rows.**  The
  multiplicity-two collision frame has zero interior defect but each of the
  five saturated boundary words is a nonidentity involution.  The screened
  finite simple overgroups likewise have no six-relator marked pair.  These
  are exact-zero checks, not a uniform proof.
- **The remaining obstruction is already qualitative.**  The normalized
  blow-up branch is excluded.  Failure of `(RHB1)` therefore produces a
  tracial matrix-ultraproduct exact model retaining a bridge, equivalently a
  nontrivial hyperlinear quotient of `Gamma_6`.  No smaller Taylor remainder
  or local packet calculation remains.
- **Scalar compression.**  It is unnecessary to prove the four individual
  bridge estimates in `(RHB1)`.  The strictly smaller finitary statement
  `atlas-six-relator-regular-face-defect-floor` asks only that the sum of the
  six nonlinear defects have a multiplicity-independent positive lower
  bound.  The fixed upper bound on five-row energy and the established
  blow-up inequality make that scalar floor quantitatively equivalent to
  the five-row lift.
