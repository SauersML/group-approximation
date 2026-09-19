---
rg: 2
id: same-orbit-closure
kind: claim
title: Same-orbit closure for the child translation images
---

On positive total trace, the two child translation images must remain inside
one source-sized paired orbit up to vanishing boundary leakage
(AGENDA 2026-08-14, "equivariant whole maps still admit rectangular
escape"). Without this closure the four-word covariance audit is
insufficient; with it, equivariant orbit-summing supplies the common
self-map law and `1/36` finishes.

Once this square source/target closure is available, no separate uniform
near-bijection theorem is needed.  The two diagonal Leavitt return laws give
square bistochastic forward/return kernels with normalized cyclic overlap
`1-o(1)`, and
`bistochastic-diagonal-return-forces-aligned-permutation` rounds each pair to
one permutation and its inverse with dimension- and alphabet-independent
loss.  Thus the load-bearing content here is exactly **same reservoir / no
rectangular enlargement**, not permutation recovery afterward.

Nor is recursive error accumulation a further gate.  If the closed reservoir
is followed through `m` binary steps, then
`closed-multiplicity-cycle-kills-carrier-trace` gives directly

```text
tr(P_0) <= 3 epsilon + ||P_m-P_0||_2/(2^m-1),
```

with no factor of `m`.  Closure supplies the returned projection; cyclic trace
then performs the entire contractive ledger automatically.

## Two sharply scoped external lessons

The positive alternative
`same-orbit-closure-from-scalable-socle-normalizer` imports the logical shape
of Li--Yang's product-socle argument: a maximal invariant local subgroup and a
transitive coordinate actor reduce enlargement to a binary choice.  The
packet must scale with the multiplicity reservoir, and the fixed-degree PI
fingerprint must exclude the full transverse branch.  A fixed finite
normalizer remains ruled out.

Wróbel, *Orbit equivalence and total weak mixing of free group actions*
([arXiv:2608.20165](https://arxiv.org/abs/2608.20165)), is only a diagnostic:
one orbit-equivalence relation can support generating actions with radically
different spectral dynamics.  Thus coarse orbit-equivalence information
cannot supply the closure sought here.  The project needs the actual
reservoir/factor support, exactly as `rectangular-escape` already shows in a
finite matrix model.
