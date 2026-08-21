---
rg: 2
id: tensor-context-classicalization-proof
kind: route
title: Joint spectral atoms turn exact tensorized row consistency into a global Boolean assignment
target: tensor-context-types-classicalize-common-source
requires: []
---

First prove joint commutativity on `Q`.  For any two variables `x,y`, choose
the fixed occurrences `c(x),c(y)`.  If they are in the same context, their
two selected label involutions commute by the local context table.  If they
are in different contexts, they commute because the two finite packets act
on different direct-product tensor factors.  By `(TCC2)`, their restrictions
are `B_xQ,B_yQ`.  Hence all shared variable involutions commute on `Q`.

For every global sign assignment `sigma in {+1,-1}^X`, form the joint
spectral projection

```text
E_sigma
 =Q product_(x in X)(I+sigma_x B_x)/2.                (TCP1)
```

The projections `E_sigma` are orthogonal and sum to `Q`.  Because `B` has no
globally satisfying assignment, every `sigma` violates some context `c`.
For that context, `E_sigma` is below the corresponding forbidden context
atom, and hence below `F_c(B_*)Q`.  Equations `(TCC2)--(TCC3)` make this
forbidden projection zero.  Therefore every `E_sigma=0`; summing `(TCP1)`
gives `Q=0`.

For the quantitative statement, use instead the commuting reference
occurrences `C_x` from `(TCC6)`.  On each joint spectral atom the scalar
`sum_c F_c(C_*)` is the number of violated contexts and is at least one.
This proves `(TCC7)`.  If

```text
E_(c,a)(D)=product_(x in c)(I+a_xD_x)/2               (TCP2)
```

is one Boolean atom, telescoping the two products and using that every
factor is a contraction yields

```text
||E_(c,a)(C)-E_(c,a)(A_c)||_2
 <=(1/2)sum_(x in c)||C_x-A_(c,x)Q||_2.               (TCP3)
```

Summing `(TCP3)` over the forbidden assignments gives `(TCC8)`.  Apply the
normalized trace to `(TCC7)`, use `|tau(T)|<=||T||_2`, and substitute
`(TCC8)`.  The resulting lower bound depends only on the fixed BCS table,
not on matrix dimension.

Finally specialize to the proposed packet construction.  On the product
selected isotypic component of `product_c K_c`, representation theory of a
finite direct product gives

```text
(tensor_c rho_c) tensor I_M.                           (TCP4)
```

Every selected context label in `(TCP4)` acts on its own `rho_c` factor.
The private compressed swap `S_c=j_cQ` changes only the role coordinate in
that same factor, so pulling the context label back to `Q` does not remove
the tensor-factor commutation.  The arbitrary external commutator in the
SMC row is common to both roles and cancels in the final D8 commutator; it
cannot carry noncommuting cross-context semantics.  Therefore the exact
hypotheses `(TCC1)--(TCC3)` are precisely what shared literal-variable rows
and exact selected SMC predicate rows impose on the product carrier, and the
preceding joint-spectrum argument applies.

