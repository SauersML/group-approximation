---
rg: 2
id: msz-polynomial-doubling-star-algebra-compiler
kind: claim
title: The MSZ machine algebra has a polynomially certified projection-doubling tape
artifacts:
  - research/artifacts/mehta-slofstra-zhao-positivity-ingestion-2026-08-20.md
distinct_from:
  fanizza-bcs-polynomial-doubling-tape: that imports the later finite-BCS packaging of this mechanism; this is the original finitely presented star-algebra compiler, including its group skeleton and exact Sobolev ledger.
  contractive-computation-ladder: that is an abstract scalar summation lemma; this supplies the concrete projections, involutions, and polynomial relator decompositions to which the summation applies.
---

For every recursively enumerable set `L` and deterministic recognizer
`M_L`, there are a fixed finite set `X`, computable finite relation sets
`R_m` in `Q Z_2^(*X)`, and words `P_tilde_n,X_tilde_n` with the following
properties.  In

```text
A_L(m)=C^*< C Z_2^(*X) : R_m >,
```

`P_tilde_n` is a hermitian-square contraction with

```text
||P_tilde_n||_1=1,       ||P_tilde_n||_(1,1)=3(n+1)/2,
```

and `X_tilde_n` is an involutive monomial of degree `4n+1`.  There are
constants `C,k,D`, independent of `m,n`, such that, whenever `M_L` has not
halted on `m` by step `n`,

```text
F_(m,n)=P_tilde_n+X_tilde_n P_tilde_n X_tilde_n-P_tilde_(n+1)=0   (MSD1)
```

in `A_L(m)`, and `F_(m,n)` has an `R_m`-decomposition of size at most

```text
C ((n+1)m)^k.                                                    (MSD2)
```

Every defining relation has first Sobolev norm at most `Dm`.  On the other
side, if `m in L`, then `A_L(m)` has a tracial state `tau` with
`tau(P_tilde_0^2)>0`.

Consequently, if `m notin L` and `tau` is a tracial
`(epsilon,R_m)`-state on `C Z_2^(*X)`, then

```text
||P_tilde_0||_tau <= Lambda m^k sqrt(epsilon).                   (MSD3)
```

Indeed tracial invariance and positivity give the level inequality

```text
||P_tilde_n||_tau
  <= 2^(-1/2)||P_tilde_(n+1)||_tau
     +2^(-1/2) C ((n+1)m)^k sqrt(epsilon),                       (MSD4)
```

and the series `sum_n n^k 2^(-n/2)` converges.

This is an additive star-algebra theorem.  Neither `(MSD1)` nor its gated
defining relation is a scalar group-word relation, so the result does not by
itself groupify the signal or produce a separated nonidentity word.
