---
rg: 2
id: bk-primitive-quotients-qd-or-traceless-force-qd
kind: claim
title: A separable nuclear stably finite C*-algebra whose primitive quotients are each quasidiagonal or traceless is quasidiagonal
distinct_from:
  gabe-traceless-exact-qd-af-embedding: that is Gabe's theorem when the whole algebra is traceless; this allows traced quasidiagonal primitive quotients and traceless non-quasidiagonal ones side by side.
  stw07-separating-qd-quotients-force-quasidiagonality: that needs a separating family of quasidiagonal quotients; this allows non-quasidiagonal traceless primitive quotients on an open set, and uses stable finiteness to make that open part compact-free.
  stw07-primitive-mf-traces-force-quasidiagonality: that requires every primitive quotient to carry a faithful MF trace; this lets primitive quotients be traceless and purely infinite.
  bk-no-compact-open-ideals-are-qd-invisible: that is the extension theorem used in the last step; this is the fibrewise dichotomy built on it.
artifacts:
  - research/artifacts/bk-t1-spectrum-simple-reduction-2026-09-12.md
---

**ESTABLISHED (Theorem 2 of the artifact; lane proof, not externally
reviewed).**  Let `E` be separable, nuclear and stably finite.  If every primitive
quotient `E/P` is quasidiagonal or traceless (every lower semicontinuous trace is
`{0,∞}`-valued), then `E` is quasidiagonal.

Consequences:

1. **UCT case (unconditional).**  Problem VII holds for every separable nuclear
   algebra with `T_1` primitive ideal space whose primitive quotients satisfy
   the UCT.  This includes all continuous `C_0(X)`-algebras with simple UCT
   fibres over locally compact Hausdorff `X`.
2. **Mixed fields.**  A stably finite continuous field may have Kirchberg-algebra
   fibres on any set of parameters and quasidiagonal fibres elsewhere.  It is
   still quasidiagonal.  No stable finiteness of the fibres is assumed.
3. **Reduction.**  Problem VII for `T_1` primitive spectra follows from its
   simple case (`bk-t1-primitive-spectrum-case`).
4. **Shape of a counterexample.**  If `E` is separable, nuclear, stably finite
   and not quasidiagonal, then `Prim(E)` has a nonempty compact open subset `W`
   in which every primitive quotient is non-quasidiagonal.  At least one
   primitive quotient over `W` carries a lower semicontinuous trace with a
   finite nonzero value.  Under the UCT that quotient is prime but not simple.

Mechanism.  The interior `V` of the non-quasidiagonal primitive ideals gives an
ideal `E_V` that is traceless (extreme traces are factorial and land in some
`E/P`, `P ∈ V`).  Being stably finite, `E_V` has compact-free spectrum by Gabe's
Corollary C.  The quasidiagonal primitive quotients are dense in the rest, so
`E/E_V` is quasidiagonal.  Theorem 1 of the spectral artifact glues the two.
