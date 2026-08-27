---
rg: 2
id: haar-tag-cancellation-kernel-proof
kind: route
title: Proof of the Haar-tag cancellation kernel dichotomy
target: haar-tag-cancellation-retention-is-group-realizability
requires:
  - character-diracization-limit
  - free-label-orthogonalization-erases-payload-trace
---

**ESTABLISHED.**

For `g=(u,h) in G`, `(HTC3)` follows directly from
`tau_H(lambda(h))=1_{h=e}`.  If `h` is nontrivial this is already the
canonical group trace.  If `h=e`, then `g` belongs to `N`; hence the trace is
canonical on all of `G` exactly when `(HTC4)` holds.

When `N={e}`, the quotient `q:G->eta(F)` is injective as well as surjective,
so the tagged representation has the canonical trace of a group isomorphic
to `eta(F)` and contains no payload trace data.  When `(HTC4)` holds, the map
`n |-> pi(n)` is injective: an element with tag `e` and payload unitary `1`
is the identity pair in `G`.  Its character is canonical by `(HTC4)`, so it
extends to the trace-preserving isomorphism `(HTC5)`.  Because `N` is normal,
the standard group-factor expectation

```text
sum_{g in G} a_g lambda(g) |-> sum_{n in N} a_n lambda(n)
```

is exactly tag-degree-zero truncation.  This proves the three alternatives
and the corner consequence, since Connes embeddability passes to von Neumann
subalgebras and nonzero finite corners.

For `(HTC7)`, apply the product trace to all tensor coordinates except the
first.  Each pair contributes
`tau(pi(w)) conjugate(tau(pi(w)))=|tau(w)|^2`.  If
`|tau(w)|=1`, equality in Cauchy--Schwarz for the faithful GNS trace gives
`pi(w)=tau(w)1`.  On a fixed finite support, every term outside `K_tau`
decays exponentially and every term in `K_tau` is already scalar.  This is
exactly `(HTC8)`.
