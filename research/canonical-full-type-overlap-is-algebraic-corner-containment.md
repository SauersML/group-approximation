---
rg: 2
id: canonical-full-type-overlap-is-algebraic-corner-containment
kind: claim
title: Full canonical overlap of finite group-algebra carriers is exactly algebraic corner containment
distinct_from:
  adjoint-reynolds-return-needs-one-overlap-moment: that uses a finite-dimensional rank mismatch to demand an approximate overlap inequality; this identifies the zero-loss endpoint for ordinary group-algebra projections in the faithful canonical trace.
  finite-product-selected-type-mark-does-not-align-carriers: that shows positive overlap is insufficient; this proves equality at the full source trace is sufficient and has no weaker hidden interpretation.
  piecewise-group-transport-gives-corner-unitaries: that constructs algebraic corner unitaries from explicit group translates; this gives the intrinsic trace criterion such a construction must satisfy.
---

Let `Gamma` be a discrete group, let `q,r in C[Gamma]` be projections, and
let `u in Gamma`.  Then

```text
tau(q u^* r u q)=tau(q)                                  (CFO1)
```

if and only if

```text
(1-r)u q=0 in C[Gamma].                                  (CFO2)
```

Equivalently, the partial group-algebra word `ruq` has full source support:

```text
(ruq)^*(ruq)=q.                                          (CFO3)
```

If also

```text
tau(r)=tau(q),                                           (CFO4)
```

then `(CFO1)` is equivalent to

```text
u q u^*=r,                                               (CFO5)
```

so the two selected carriers are exactly conjugate in the group algebra.

## Proof

Since `r` is a projection,

```text
tau(q)-tau(q u^*r u q)
 =tau(q u^*(1-r)u q)
 =||(1-r)u q||_2^2.                                     (CFO6)
```

The canonical trace is faithful on `L(Gamma)`, hence the right side vanishes
if and only if `(1-r)u q=0`.  All factors have finite group support, so zero
in `L(Gamma)` is zero already in `C[Gamma]`.  This proves `(CFO1)--(CFO3)`.

Equation `(CFO2)` says `uqu^*<=r`.  Under `(CFO4)` the two projections have
equal faithful trace, so the inclusion is equality, proving `(CFO5)`.

The argument works unchanged for an algebraic corner transport

```text
V=sum_i g_i p_i in C[Gamma]
```

after replacing `uq` by `Vq`: equality of its source overlap with `tau(q)`
is equivalent to the corresponding finite group-algebra defect being zero.

## Consequence for canonical selected-type alignment

Canonical trace does remove noncanonical forbidden-sector representations,
but it does not turn a strict overlap inequality into type preservation.  A
zero-loss alignment of rational packet projections is precisely an algebraic
corner-containment identity.  Therefore the canonical-profile Fanizza route
has two genuinely different options:

1. construct finite-support corner partial isometries satisfying `(CFO2)`
   and the required shared-variable intertwining identities; or
2. prove a matrix-only theorem which can tolerate a quantified overlap loss
   while still collapsing the Fanizza mark.

The first option is the signed-Hecke/block-escaping algebraic atlas problem.
The second is an analytic common-carrier theorem.  Merely knowing that a
chain product is nonzero lies strictly between neither endpoint, by
`finite-product-selected-type-mark-does-not-align-carriers`.

## Claim boundary

This is an exact canonical-trace statement.  It does not claim that an
approximately full overlap has no useful quantitative consequences; in
finite matrices `(CFO6)` gives exactly the Hilbert--Schmidt leakage that such
a theorem would have to charge.
