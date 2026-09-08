---
rg: 2
id: tracial-moment-relaxations-cannot-certify-the-leavitt-gap
kind: claim
title: Every finite tracial moment level in the four Leavitt generators has optimum zero
invalidates:
  - leavitt-uniform-gap-via-tracial-moment-certificate
distinct_from:
  leavitt-24k-feasibility-has-a-uniform-gap: that asks for a dimension-uniform normalized-HS gap, which would prove nonhyperlinearity; this proves that one named family of certificates can never produce such a gap, and decides neither branch.
  binary-leavitt-hyperlinear-iff-24k-feasible: that is the equivalence between hyperlinearity and vanishing of the relative-unitary infima; this is a statement about a relaxation of that optimization, whose optimum is zero whether or not the infima vanish.
  finite-npa-nonexactness-does-not-separate-qc: that is about finite NPA levels failing to equal the quantum set in nonlocal-game scenarios, and carries no separation; this is one group, one generating set, and an exact zero-error feasible point at every level, so the failure is total rather than asymptotic.
  leavitt-24k-models-avoid-blockwise-error-basis-normalizers: that excludes a class of models by a trace gap, and is a genuine partial obstruction; this excludes a class of proofs, and is a limitation of a method.
artifacts:
  - research/artifacts/leavitt-tracial-moment-relaxation-no-go-2026-09-08.md
---

**ESTABLISHED.**  Let `F` be free on `c,b_1,b_2,b_3`, let
`q : F -> H = L_(F_2)(1,2)^x` be the surjection of
`binary-leavitt-units-generated-by-c3-and-c2-cubed` (its kernel containing
the internal relators of `P = C_3 * C_2^3`), and set

```text
y_w = 1 if q(w) = 1,      y_w = 0 otherwise.                      (TM1)
```

Then for every finite word set `W` the moment matrix
`(y_(u^-1 v))_(u,v in W)` is positive semidefinite, and `(TM1)` satisfies
normalization, traciality, every true relation identity `y_(arb)=y_(ab)`
for `r in ker q`, and the exact normalized regular characters on both
embedded finite factors.

Consequently, for every finite `T` contained in `ker q`, the squared
defect energy of the ordinary tracial moment relaxation in these four
generators,

```text
E_T = sum_(r in T) (2 - y_r - y_(r^-1)),                          (TM2)
```
has value `0` at this point, and `0` is also its trivial lower bound.  So

```text
every finite level of the relaxation has optimum exactly zero,           (TM3)
```
and this is unchanged by adjoining further true group relations of `H` or
further prescribed canonical moments, since `(TM1)` satisfies those too.

**Certificate form.**  On `C H` let `tau` be the coefficient of the
identity.  Then `tau(a^*a) = sum_h |alpha_h|^2 >= 0` and
`tau(ab) = tau(ba)`.  Any contradiction derived only from positivity,
traciality, the true group relations and the prescribed character values
would also hold under `tau`, where every relator defect vanishes.  Hence
no sum-of-squares certificate with only those universally tracial premises
can give a strictly positive lower bound for `(TM2)`.

**Scope, stated sharply.**  This is a limitation of one certificate
method, not an obstruction to the group and not evidence of
hyperlinearity.  It supplies no finite-dimensional models and no relative
unitary; `(TM1)` specifies no `U` in the parametrization of
`binary-leavitt-hyperlinear-iff-24k-feasible`.  It does not assert that
every method exploiting matrix dimension must fail — the gap between a
positive tracial functional on `C H` and approximating finite-dimensional
traces is exactly the open question
`leavitt-24k-feasibility-has-a-uniform-gap`.

DERIVATION
tracial-moment-relaxation-zero-optimum-proof
