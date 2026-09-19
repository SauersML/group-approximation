---
rg: 2
id: stw09-local-mf-corner-traces-across-qd-extension-force-qd
kind: claim
title: Local MF corner traces across a quasidiagonal extension force quasidiagonality
distinct_from:
  stw09-jointly-faithful-mf-traces-force-mf: that theorem combines tracial states defined on the whole algebra; the corner traces here need not extend tracially to the ambient algebra, and norm recovery instead uses a quasicentral projection cut together with the quotient.
  stw07-primitive-mf-traces-force-quasidiagonality: that pulls traces back along quotient homomorphisms from every primitive quotient; compression to a noncentral hereditary corner is not a homomorphism, so this uses a different two-block gluing argument.
  stw07-surjective-pullbacks-preserve-nuclear-qd-finiteness: that embeds a pullback into a direct sum of two quasidiagonal coordinate algebras; a general extension has no such coordinate embedding, and the present theorem uses its quasicentral projectional approximate unit.
  stw07-local-qd-subalgebras-force-quasidiagonality: that requires norm approximation of the ambient packet by one quasidiagonal subalgebra of A; neither the ideal corner nor the quotient embeds as such an ambient norm approximation here.
  stw82-raw-two-cut-reuse-iff-quasidiagonal: that characterizes when an extension admits quasicentral projectional cuts; this uses those cuts to glue norm-detecting matrix models from the ideal corners and quotient.
artifacts:
  - research/artifacts/stw09-ix1-separating-mf-traces-audit-2026-08-30.md
---

Let `A` be a separable unital C-star algebra and let `I` be a proper closed
two-sided ideal.  Consider

```text
0 -> I -> A -> A/I -> 0
```

and suppose that `I` has an increasing approximate unit of projections
`(p_n)` which is quasicentral in `A`.  If every nonzero unital corner
`p_n A p_n` and the quotient `A/I` are quasidiagonal, then `A` is
quasidiagonal.

Consequently, let `A` be a separable unital nuclear C-star algebra with a
faithful tracial state `tau`.  Suppose there is an ideal `I` with such a
quasicentral projectional approximate unit and:

1. for every nonzero `p_n`, the normalized corner trace

   ```text
   tau_n=tau(p_n)^(-1) tau|p_n A p_n
   ```

   is an MF trace;
2. `A/I` is quasidiagonal (equivalently MF, since it is nuclear).

Then `A` is quasidiagonal.  This is an unconditional UCT-free positive
class for STW Problem IX(1).

No ambient MF trace is assumed, and the given `tau` is not asserted to be
MF.  In particular, this condition is not subsumed by requiring the
faithful trace to lie in the weak-star
closed convex hull of MF traces on `A`: a trace on a noncentral hereditary
corner generally has no tracial extension to `A`.  The local MF trace is
used only to make its corner algebra MF by faithfulness; nuclearity then
makes that corner quasidiagonal.  The quasicentral cut and the quotient
recover the two central-support pieces of the ambient norm.
