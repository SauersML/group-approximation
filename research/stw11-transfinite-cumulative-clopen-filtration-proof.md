---
rg: 2
id: stw11-transfinite-cumulative-clopen-filtration-proof
kind: route
title: Build the open-support ideal forward and make one projectional cut at the terminal support
target: stw11-transfinite-cumulative-clopen-filtrations-glue-qd
requires:
  - stw09-local-mf-corner-traces-across-qd-extension-force-qd
  - stw07-local-qd-subalgebras-force-quasidiagonality
artifacts:
  - research/artifacts/stw11-transfinite-clopen-filtration-audit-2026-08-30.md
---

Write

```text
A=C(X) rtimes Z^d,
I_beta=C_0(U_beta) rtimes Z^d.
```

Amenability of `Z^d` makes crossed products exact.  Thus, at a successor
stage,

```text
0 -> I_beta -> I_(beta+1)
  -> C_0(Y_beta\Y_(beta+1)) rtimes Z^d -> 0.             (CF1)
```

We prove by transfinite induction that every `I_beta` is quasidiagonal.
The assertion is trivial at `beta=0`.  Suppose first that `I_beta` is
quasidiagonal.  Choose an invariant compact-open exhaustion `(K_n)` of
`U_beta`, omitting this step when `beta=0`, and put `p_n=1_(K_n)`.  Since
`U_beta` is open in `X`, a subset compact-open in `U_beta` is open in `X`
and compact, hence clopen in `X`.  Invariance therefore makes `p_n` a
central projection of `A`, and `(p_n)` is an approximate unit for
`I_beta`.  Moreover,

```text
p_n I_(beta+1) p_n = p_n I_beta p_n.                    (CF2)
```

The right side is a corner of the quasidiagonal algebra `I_beta`, hence is
quasidiagonal.  Unitize `(CF1)`.  Its quotient is the unitization of the
quasidiagonal successor stratum, while `(p_n)` is still a quasicentral
projectional approximate unit and its corners are the algebras in `(CF2)`.
The two-cut extension theorem
`stw09-local-mf-corner-traces-across-qd-extension-force-qd` makes
`I_(beta+1)` quasidiagonal.  For `beta=0`, `(CF1)` directly identifies
`I_1` with the first successor stratum.

Now let `delta<=lambda` be a nonzero limit ordinal.  Continuity of the
closed-set chain gives

```text
U_delta=union_(beta<delta) U_beta.
```

Compact support and density of the algebraic crossed product give

```text
I_delta=closure(union_(beta<delta) I_beta).              (CF3)
```

Indeed, every compact subset of `U_delta` is covered by finitely many of
the increasing open sets `U_beta`, hence lies in one of them.  The
injective directed-union consequence of
`stw07-local-qd-subalgebras-force-quasidiagonality`, applied after
unitization, makes `I_delta` quasidiagonal.  This completes the induction.
This argument does not use countable cofinality: the finite subcover has a
largest ordinal index.

Finally use

```text
0 -> I_lambda -> A -> C(Y_lambda) rtimes Z^d -> 0.       (CF4)
```

The compact-open exhaustion of `U_lambda` gives central projections forming
an approximate unit for `I_lambda`.  Every resulting corner of `A` lies in
the quasidiagonal ideal `I_lambda`, so it is quasidiagonal.  The quotient
in `(CF4)` is quasidiagonal by hypothesis.  One last application of the
two-cut extension theorem proves that `A` is quasidiagonal.  If
`Y_lambda` is empty, then `A=I_lambda` and this last cut is unnecessary.

The cumulative hypothesis is exactly what makes `(CF2)` available.  A
compact-open subset of the relative stratum `Y_beta\Y_(beta+1)` need not be
open in `X`, so separate stratum exhaustions alone do not provide a
quasicentral projectional approximate unit for the growing ideal.
