---
rg: 2
id: sl3-re-over-lattice-iff-re-over-scalars
kind: claim
title: Relative embeddability of the SL3 arithmetic inclusion over its lattice factor is equivalent to relative embeddability over scalars
artifacts:
  - research/artifacts/gao-relative-embeddability-appendix-sl3-audit-2026-08-21.md
distinct_from:
  sl3-arithmetic-double-hyperlinear-iff-relative-embeddable: that identifies canonical-trace embeddability of the arithmetic double with RE over the lattice factor; this removes the coefficient factor from the RE condition itself.
  arithmetic-pair-is-not-relatively-embeddable: that is the desired negative statement; this is an unconditional equivalence between its lattice-coefficient and scalar-coefficient formulations.
---

Put

```text
C = SL_3(Z),  A = SL_3(Z[1/2]),
N = L(C) subset M = L(A).
```

Then

```text
N subset M is RE/N    iff    N subset M is RE/C_scalar.      (RCE1)
```

Here `C_scalar` denotes the scalar von Neumann algebra, not the arithmetic
group `C`.

The forward implication is Gao, arXiv:2012.07940, Proposition 2.2.  The
factor `N` is Connes embeddable because `C` is residually finite; hence `N`
is QWEP, and Gao's proposition removes a QWEP coefficient algebra from an
RE model.  Conversely the scalar algebra embeds unitally in `N`, so the
coefficient-enlargement part of the same proposition sends every
`RE/C_scalar` model to an `RE/N` model.

Consequently Gao's commuting-square model may be sought with no auxiliary
copy of `N`: it consists of a trace-preserving embedding

```text
M -> prod_omega A_k
```

and hyperfinite `B_k subset A_k`, with `A_k` finite QWEP, such that the
image of `N` lies in `prod_omega B_k` and the square with `N subset M`
commutes.  Thus the exact remaining obstruction is a pure hyperfinite-
carrier microstate obstruction rather than an interaction with a second
lattice-factor coordinate.

