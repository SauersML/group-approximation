---
rg: 2
id: stw99-problem-viii-exact-quasidiagonal-af-embeddable
kind: claim
title: Every separable exact quasidiagonal C*-algebra is AF-embeddable (STW Problem VIII)
root: true
distinct_from:
  stw99-problem-vii-blackadar-kirchberg: that asks whether stable finiteness forces quasidiagonality; this starts from quasidiagonality and asks for the stronger AF-embeddability, with exactness in place of nuclearity.
artifacts:
  - research/artifacts/nuclear-99-problems-ingestion-2026-08-27.md
  - research/artifacts/stw08-af-embedding-status-and-coherence-audit-2026-08-30.md
---

**Problem VIII of Schafhauser--Tikuisis--White, *Nuclear C\*-algebras: 99 problems*, arXiv:2506.10902.**  Is every separable exact quasidiagonal
C\*-algebra AF-embeddable?

AF-embeddability implies quasidiagonality, and for separable exact algebras no
other obstruction is known.  Blackadar--Kirchberg ask the nuclear version
(Math. Ann. 307 (1997), Question 7.3.3).  Known: Theorem 11 of STW ---
separable exact UCT algebras embed into a unital simple AF algebra exactly
when they have a faithful amenable trace (Tikuisis--White--Winter, Gabe,
Schafhauser) --- and Gabe's traceless case (STW Theorem 13), and Pimsner's
`C(X) ⋊ ℤ` (STW Theorem 14).  The special case with a faithful quasidiagonal
trace is Problem IX(2) (`stw99-problem-ix2-exact-faithful-qd-trace-af-embeddable`).

## New unconditional permanence

`stw08-finite-group-crossed-products-preserve-af-embeddability` proves that
AF-embeddability survives every finite-group crossed product.  Its regular
covariant representation embeds `A rtimes F` directly into
`M_|F|(E)` from any embedding `A->E` with `E` AF; the action need not extend
to `E`.  Consequently all finite transformation-group algebras
`C_0(X) rtimes F` are AF-embeddable, and AF-embeddability of amenable group
C*-algebras passes from a finite-index subgroup to the whole group even when
the subgroup is nonnormal and the extension is nonsplit.

This does not solve Problem VIII: the finite regular representation
transports an AF embedding but does not manufacture one from unrelated
quasidiagonal models.
