---
rg: 2
id: tracial-moment-relaxation-zero-optimum-proof
kind: route
title: The indicator of the kernel is a Gram matrix in the regular representation
target: tracial-moment-relaxations-cannot-certify-the-leavitt-gap
requires:
  - binary-leavitt-units-generated-by-c3-and-c2-cubed
artifacts:
  - research/artifacts/leavitt-tracial-moment-relaxation-no-go-2026-09-08.md
---

## Proof

**Positivity.**  In `l^2(H)` with orthonormal basis `(e_h)_(h in H)`,
assign to a word `w` the vector `e_(q(w))`.  Then

```text
<e_(q(u)), e_(q(v))> = 1_(q(u)=q(v)) = y_(u^-1 v),
```
because `q(u) = q(v)` exactly when `q(u^-1 v) = 1`.  So the moment matrix
is a Gram matrix, hence positive semidefinite.  Explicitly, for finitely
many coefficients,

```text
sum_(u,v) conj(alpha_u) alpha_v y_(u^-1 v)
  = sum_(h in H) | sum_(w : q(w) = h) alpha_w |^2 >= 0.            (1)
```

**Normalization, conjugation, traciality.**  `y_1 = 1` since `q(1) = 1`.
`y_(w^-1) = y_w = conj(y_w)`, the values being real.  Traciality is
`y_(uv) = y_(vu)`, which holds because `q(uv) = 1` iff `q(vu) = 1`: the
two images are conjugate, `q(vu) = q(u)^-1 q(uv) q(u)`.

**Relation identities.**  For `r in ker q` and any words `a,b`,
`q(arb) = q(a)q(b) = q(ab)`, so `y_(arb) = y_(ab)`.  This covers relation
words inserted on either side, which is what a moment level imposes.

**Character conditions.**  The prerequisite proves `A = <c> = C_3` and
`B = <b_1,b_2,b_3> = C_2^3` are subgroups of `H` of orders exactly three
and eight; in particular both inject.  So for an element of either factor,
`(TM1)` takes the value one at its identity and zero elsewhere, which is
precisely its normalized regular character — the data the `24k` criterion
prescribes on the two frozen factors.

**The optimum.**  For a unitary word `r(X)`,
`||r(X) - I||_2^2 = 2 - tr(r(X)) - tr(r(X)^*)`, so the relaxation's
objective is `(TM2)`.  Each summand is a squared norm in any feasible
interpretation, hence nonnegative, giving the lower bound `0`; and
`(TM1)` attains `0` because every `r in T` lies in `ker q`, so
`y_r = y_(r^-1) = 1`.  Since `(TM1)` is feasible at every level — the
level only ever imposes more of the conditions just verified — every
finite level has optimum `0`, which is `(TM3)`.

**Certificate form.**  On the group algebra `C H`, `tau(sum alpha_h h)`
is `alpha_1`.  Then `tau(a^*a) = sum_h |alpha_h|^2 >= 0` and
`tau(ab) = tau(ba)` by inspecting which products contribute the identity.
Under `tau`, every relator of `H` evaluates to the identity element, so
every defect `2 - tau(r) - tau(r^*)` vanishes.  A derivation using only
positivity, traciality, the group relations and the character values is
therefore sound for `tau` and cannot conclude a strictly positive lower
bound.
