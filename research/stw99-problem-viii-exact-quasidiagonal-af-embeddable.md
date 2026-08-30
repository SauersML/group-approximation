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

There is now a separate continuous-gluing permanence theorem.
`stw08-continuous-block-gluings-preserve-af-embeddability` embeds
`C_0(X,A)` into an AF algebra whenever `X` is second-countable locally
compact and `A` is AF-embeddable, by pulling back functions along a Cantor
surjection onto the one-point compactification.  Every C*-subalgebra of a
finite direct sum of such blocks is therefore AF-embeddable.  In particular,
arbitrary finite pullback trees, mapping tori, and finite recursive
subhomogeneous constructions are covered constructively; no gluing map is
required to be surjective.

These results do not solve Problem VIII: both the finite regular
representation and the continuous-coordinate construction transport AF
embeddings already available on their input pieces, but neither manufactures
one from unrelated quasidiagonal models.
