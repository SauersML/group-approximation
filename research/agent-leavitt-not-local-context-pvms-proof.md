---
rg: 2
id: agent-leavitt-not-local-context-pvms-proof
kind: route
title: Partition the marked spin spectral atoms by allowed local assignments
target: agent-leavitt-not-local-context-pvms
requires:
  - agent-leavitt-local-spin-corner
  - paddock-slofstra-bcs-forbidden-projection-dictionary
---

Write `X_1,...,X_d` for the commuting involutions in the extraspecial group
`E_d` of the prerequisite and `P=(1-z)/2`.  For
`epsilon=(epsilon_1,...,epsilon_d) in {0,1}^d`, put

```text
e_epsilon = 2^(-d) P product_(i=1)^d
                         (1+(-1)^(epsilon_i)X_i).       (LPP1)
```

This is an explicit finite linear combination of group elements.  The
factors commute with one another and with `P`.  The elementary identities

```text
(1+X_i)(1-X_i)=0,       (1+X_i)+(1-X_i)=2              (LPP2)
```

show directly that the `e_epsilon` are mutually orthogonal projections
summing to `P`.  They are nonzero: under the isomorphism

```text
P C[E_d]P ~= M_(2^d)(C)                                (LPP3)
```

from `agent-leavitt-local-spin-corner`, `X_i` is Pauli `Z` in tensor slot
`i`, so `(LPP1)` is a rank-one coordinate projection.

For each context `c`, choose any surjection

```text
f_c:{0,1}^d -> R_c,                                    (LPP4)
```

which exists by `(LCP1)`, and define

```text
p_(c,a)=sum_(epsilon: f_c(epsilon)=a) e_epsilon.        (LPP5)
```

Surjectivity and orthogonality prove all projection assertions in `(LCP2)`.
Formula `(LCP3)` is therefore the joint functional calculus of this PVM:
each `V_(c,x)` is a self-adjoint involution, the variables of a fixed context
commute, and every forbidden joint spectral projection is zero.  By the
Paddock--Slofstra projection dictionary this is exactly the local BCS
predicate relation.

Finally suppose all overlap equations `(LCP4)` also hold.  Evaluation on the
one-dimensional range of `e_epsilon` is a character of the common diagonal
algebra.  For every variable `x`, `(LCP4)` makes its resulting sign
independent of the context containing `x`; call that sign `a_epsilon(x)`.
For each context `c`, `(LPP5)` says that the restriction of
`a_epsilon` to `U_c` equals the allowed assignment `f_c(epsilon)`.  Hence
`a_epsilon` is a global classical satisfying assignment.  Applied to
`B_loop`, this contradicts its strict quantum, and therefore classical,
value gap.  This proves both the construction and its exact stated limit.

