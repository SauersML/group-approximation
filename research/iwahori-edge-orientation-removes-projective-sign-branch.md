---
rg: 2
id: iwahori-edge-orientation-removes-projective-sign-branch
kind: claim
title: The Iwahori edge orientation removes the balanced projective block-flip branch
artifacts:
  - research/artifacts/canonical-iwahori-projective-sign-resolution-2026-08-22.md
distinct_from:
  canonical-trace-square-is-blind-to-iwahori-overlap: that exhibits one isolated balanced block flip invisible to trace square; this proves that a projectively central family over the entire second modular vertex cannot retain that flip while commuting with the common Iwahori edge.
  iwahori-projection-overlap-is-a-spherical-coefficient: that expresses ordinary overlap as one positive-definite coefficient; this gives the exact quadratic relation between overlap and projective trace-square energy and resolves its second zero.
  projective-commutant-transfer-for-arithmetic-pair: that is the open approximate arithmetic transfer theorem; this proves that its projective conclusion is already strong enough for ordinary Iwahori projection transfer.
---

Let `C=SL_2(Z)`, let `B<C` be either index-three Iwahori subgroup, and let
`pi_n:C->U(d_n)` be exact representations.  Suppose `P_n` are projections,
put `V_n=2P_n-1`, and assume

```text
max_(b in S_B)||[V_n,pi_n(b)]||_2 ->0.                (IER1)
```

For a unitary `U`, write

```text
r(P,U)=||[P,U]||_2^2,
e(V,U)=1-|tr([V,U])|^2.
```

Then the exact identity

```text
e(2P-1,U)=4 r(P,U)(1-r(P,U))                         (IER2)
```

holds.  Indeed, if `t=tr(P)` and
`alpha=tr(PUPU^*)`, then `r=2(t-alpha)` and

```text
tr(VUVU^*)=1-4(t-alpha)=1-2r.
```

Now assume in addition that

```text
max_(c in S_C)e(V_n,pi_n(c))->0.                     (IER3)
```

Then

```text
max_(c in S_C)||[P_n,pi_n(c)]||_2 ->0.               (IER4)

```

The point is that `(IER2)` alone has two branches: `r->0` and `r->1`.
For each generator, `(IER3)` makes `Ad(pi_n(c))V_n` close either to `V_n`
or to `-V_n`.  After a subsequence the signs stabilize.  Exact
multiplication in `pi_n` makes those signs a character

```text
chi:C-> {+1,-1}.
```

Condition `(IER1)` makes `chi` trivial on `B`.  But the only nontrivial
sign character of `SL_2(Z)` is the mod-two sign character: under
`SL_2(F_2)=S_3`, the Iwahori subgroup maps onto a transposition subgroup, so
that character is nontrivial on `B`.  Hence `chi` is trivial and only the
`r->0` branch occurs, proving `(IER4)`.

Consequently projective trace-square transfer for the arithmetic pair is
already sufficient for `canonical-iwahori-projection-commutant-transfer`.
Apply it to `V_n=2P_n-1` and the canonical approximate amalgam tuple.  The
first-vertex ordinary commutators make all subgroup projective energies tend
to zero; projective transfer makes `(IER3)` hold on the second vertex; the
common edge gives `(IER1)`; and the sign-resolution argument yields ordinary
second-vertex commutation.

This does not prove the missing approximate projective transfer theorem.
It proves that no additional coordinate-Pauli orientation gadget is needed
after that theorem: the native Iwahori edge itself authenticates the sign.
Conversely, trace-square control of a single second-vertex word remains
insufficient, since signs become constrained only when the full finite
vertex presentation and the edge generators are used together.

