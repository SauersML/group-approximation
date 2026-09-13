---
rg: 2
id: stw07-qd-radical-criterion-compact-open
kind: claim
title: A separable nuclear C*-algebra is quasidiagonal iff its quasidiagonal radical has no compact open primitive subset, so a counterexample has a traced compact ideal in its radical
distinct_from:
  stw07-separating-qd-quotients-force-quasidiagonality: that constructs the radical R_qd and the largest quasidiagonal quotient; this characterises exactly when the radical is harmless and locates a traced compact ideal inside it.
  stw07-counterexample-has-singular-trace-normal-form: that finds an unbounded trace on the stable kernel of a unitized counterexample; this finds a compact ideal with a nontrivial lower semicontinuous trace inside the quasidiagonal radical of any counterexample.
  bk-no-compact-open-ideals-are-qd-invisible: that is the extension theorem for compact-free ideals; this applies it to the radical to get an exact criterion.
artifacts:
  - research/artifacts/bk-spectral-extension-permanence-2026-09-12.md
---

**ESTABLISHED (Theorem 3 and Corollary 4 of the artifact).**  Let `E` be
separable and nuclear, and `R_qd(E) = ∩ {J : E/J quasidiagonal}`.  Then `E` is
quasidiagonal iff `Prim(R_qd(E))` has no nonempty compact open subset.

Consequently, if `E` is a negative answer to STW Problem VII (separable,
nuclear, stably finite, not quasidiagonal), then:

1. `R_qd(E)` contains a nonzero compact ideal `K` of `E`;
2. every such `K` is separable, nuclear and stably finite, and is not traceless:
   some lower semicontinuous trace on `K` takes a value in `(0, ∞)`;
3. in the stable-character normal form `E = (A ⊗ K)~`, all of this happens
   inside the stable kernel `A ⊗ K`.

So whatever obstructs quasidiagonality lives in compact, traced pieces of the
radical.  Traceless pieces and compact-free pieces are invisible.  The residual
problem is how traced compact ideals are glued into `E`.
