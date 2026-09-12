---
rg: 2
id: opnorm-hs-ledger-incomparability-proof
kind: route
title: Compute both floors of the same off-diagonal row and compare them at vanishing density
target: opnorm-return-row-cannot-come-from-an-hs-ledger
requires:
  - rank-deficient-return-row-has-operator-norm-one
  - one-coarse-to-fine-prefix-isometry-closes-the-reservoir
---

`(LDG1)` is the standard pair of comparisons on `M_d(C)`.  For the left
inequality, `tau(A^*A)<=||A||_op^2` because `A^*A<=||A||_op^2`.  For the
right, `||A||_op<=||A||_(HS)=sqrt(d)||A||_2`, since the largest singular
value is at most the root of the sum of their squares.  Both are attained:
the left at a unitary multiple of a projection, the right at a rank-one
operator.

`(LDG3)` is `(ROW7)` of `rank-deficient-return-row-has-operator-norm-one`,
using `rank(e)=rank(P)/r>rank(P)/s=rank(f)` for `P!=0`.

For `(LDG2)` compute the unnormalized Hilbert--Schmidt mass directly:

```text
tr(L^*L)=tr(eJ^*(1-f)Je)=tr(e)-tr(eJ^*fJe)
        =rank(e)-tr((J^*fJ)e).
```

The second term is the trace of a product of two projections, so it lies in
`[0, min(rank(e),rank(f))] = [0, rank(f)]`.  Hence

```text
rank(e)-rank(f) <= tr(L^*L) <= rank(e),
```

and dividing by `d` with `rank(e)=rank(P)/r`, `rank(f)=rank(P)/s` gives
`(LDG2)`.  The lower half is the floor `(CFI2)` of
`one-coarse-to-fine-prefix-isometry-closes-the-reservoir` specialized to
`X=fJe`, via the identity `e-X^*X=L^*L` of `(ROW2)`; the upper half is the
new content, and it is what makes clause 2 sharp rather than merely a failed
inequality.

**Clause 1.**  Immediate from the left half of `(LDG1)`.

**Clause 2.**  By `(LDG2)`, `||L||_2<=sqrt(tau(P)/r)`, and by `(LDG3)`,
`||L||_op=1`.  Take any sequence of coordinates in which the recovered
carrier has `tau(P_n)->0` -- which is exactly the regime the positive-density
machinery exists to exclude, and which nothing in the corona hypotheses rules
out on its own.  Along it, `||L_n||_2 -> 0` while `||L_n||_op = 1`.  So no
implication `||L||_2<=omega ==> ||L||_op<=omega'(omega)` with a
density-independent `omega'` can hold, and the `sqrt(d)` factor of `(LDG1)`
is attained up to the absolute constants of `(LDG2)`.

**Clause 3 and the operational rule.**  A ledger estimate is by construction
a bound on a trace of a positive expression, hence on `||.||_2` of the
corresponding operator; clause 2 says every such bound is consistent with
`(LDG3)`.  Therefore no composition of such estimates can output the
operator-norm row, whatever the intermediate combinatorics.  Conversely
nothing in this argument bounds the operator-norm row from above, so the
claim is a transfer no-go and not an obstruction to the row itself.
