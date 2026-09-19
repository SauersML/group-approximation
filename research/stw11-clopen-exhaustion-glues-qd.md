---
rg: 2
id: stw11-clopen-exhaustion-glues-qd
kind: claim
title: Compact-open invariant exhaustions glue quasidiagonality across dynamical support extensions
distinct_from:
  stw99-problem-xi-zd-crossed-stably-finite-qd: that asks whether stable finiteness alone forces quasidiagonality and AF-embeddability; this gives an exact quasidiagonal-extension criterion and assumes quasidiagonality on the compact support cuts and the terminal quotient.
  stw09-local-mf-corner-traces-across-qd-extension-force-qd: that is an abstract C-star extension theorem; this proves that a concrete topological condition on an invariant open stratum automatically supplies its quasicentral projectional hypothesis and iterates it along a finite dynamical filtration.
artifacts:
  - research/artifacts/stw99-xi-clopen-support-gluing-2026-08-30.md
---

Let `Z^d` act on a compact metrisable space `X`, let `Y subseteq X` be
closed and invariant, and put `U=X\Y`.  Suppose that `U` has an increasing
exhaustion

`K_1 subseteq K_2 subseteq ...`,  `union_n K_n=U`,

by compact-open invariant subsets of `U`.  If

`C(K_n) rtimes Z^d`

is quasidiagonal for every nonempty `K_n`, and

`C(Y) rtimes Z^d`

is quasidiagonal, then `C(X) rtimes Z^d` is quasidiagonal.

In particular, write `A=C(X) rtimes Z^d` and
`I=C_0(U) rtimes Z^d`.  The conclusion holds if:

1. `A` is stably finite;
2. `I` is traceless;
3. `Y` carries an invariant probability measure with support all of `Y`.

This is a mixed positive class beyond both global solved extremes.  If
`I!=0`, every bounded trace on `A` vanishes on `I` (its restriction is a
bounded tracial weight on the traceless ideal), so `A` has no faithful
trace; meanwhile the quotient trace shows that `A` is not traceless.

More generally, let

`X=Y_0 supseteq Y_1 supseteq ... supseteq Y_s`

be a finite chain of closed invariant subsets.  If every stratum
`Y_(j-1)\Y_j` has such a compact-open invariant exhaustion, all crossed
products of the compact exhaustion pieces are quasidiagonal, and the
terminal crossed product `C(Y_s) rtimes Z^d` is quasidiagonal, then
`C(X) rtimes Z^d` is quasidiagonal.

The result is unconditional and does not assert AF-embeddability.  That
upgrade cannot be inferred merely from the resulting quasidiagonality:
doing so would import the still-open exact quasidiagonal-to-AF problem.
