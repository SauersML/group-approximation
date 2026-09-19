---
rg: 2
id: common-reflection-defect-is-holonomy-spectator
kind: claim
title: A common reflection defect cannot repair accepting-corner holonomy
distinct_from:
  root-block-piecewise-transport-cannot-host-nonce-bcs: that excludes a completed atlas lying in the finite root block; this identifies why adjoining a common complementary defect does not alter the residual cycle problem.
  common-meet-local-sectors-pay-one-deficit: that is an analytic density estimate; this is an exact corner-algebra splitting statement.
---

**ESTABLISHED.**  Let `A` be a unital star algebra, let `p=e+q` be a sum of
orthogonal projections, and let `(f_i)` be a complete projection partition
of `q`.  If a unitary `W in pAp` transports this partition to another
complete partition of the **same** carrier `q`, then

```text
WqW^*=q,       Wq=qW,       We=eW,                         (RHS1)
```

and `qWq` is a unitary of `qAq`.  Consequently every product of such context
transporters restricts on `q` to the product of their `q`-corner
restrictions.  The `e` block contributes only an independent unitary and no
cross term can change a return map or cycle holonomy on `q`.

More generally, in any finite tracial C-star algebra, if an ambient unitary
`U` has **unitary compression** `qUq` in `qAq`, then `Uq=qU` already.  Thus
even a literal ambient group word cannot make a cross-block excursion while
decoding an exact unitary observable on `q`.  This applies in particular to
the self-adjoint involutions used for BCS variables.

In particular, a rank-one standard or hyperoctahedral reflection defect is a
pure density spectator once every BCS context is required to use the same
accepting carrier `q`.  Free-phase conjugates which fix the common defect
reduce on `q` to exactly the existing signed-Hecke one-marginal cells.  The
first non-tree cycle is therefore literally the existing
`signed-hecke-block-escaping-cycle-holonomy` gate; the reflection supplies
no new multi-piece wordization.  Mixing `e` with `q` cannot evade this:
transporting a complete `q` partition back to a complete `q` partition
already forces `(RHS1)`.

DERIVATION
common-reflection-defect-is-holonomy-spectator ✓ via common-reflection-defect-spectator-proof

CANONICAL MATERIAL TO READ
research/common-reflection-defect-spectator-proof.md
research/signed-hecke-block-escaping-cycle-holonomy.md
