---
rg: 2
id: bk-type-i-case-via-k0-embedding
kind: route
title: Climb a composition series with CCR subquotients, gluing each step by Spielberg and Brown-Dadarlat Proposition 4.6
target: bk-type-i-stably-finite-algebras-are-qd
requires:
  - type-i-qd-algebras-have-k0-embedding-property
  - brown-dadarlat-ext-trivial-class-gives-qd-extension
  - separable-ccr-algebras-are-quasidiagonal
artifacts:
  - research/artifacts/bk-type-i-k0-embedding-equivalence-2026-09-16.md
---

Full proof: artifact §3, proof of (b) ⇒ (a).  Standard facts (T1)--(T4), (Q1),
(S1) and (K1) are listed in artifact §0, with citation status.

Let `E` be separable, stably finite and type I.  Take a composition series
`(I_α)_{α ≤ β}` with `I_{α+1}/I_α` CCR (Dixmier, Pedersen; numbering not
re-checked).  It is countable, since `Prim(I_α)` strictly increases in the
second countable space `Prim(E)`.  Induct on `α`.

- **Limit ordinals.**  An increasing union of QD ideals has QD closure.
- **Successor `α + 1`.**
  - `I_α` is separable, QD and type I.
  - `B = I_{α+1}/I_α` is separable and CCR.  So it is QD by
    `separable-ccr-algebras-are-quasidiagonal`, nuclear, and UCT
    (Rosenberg--Schochet; not re-checked).
  - `I_{α+1}` is a C\*-subalgebra of `E`, hence stably finite.
  - Stabilise: `0 → K⊗I_α → K⊗I_{α+1} → K⊗B → 0`.  All three terms are stably
    finite.
  - Spielberg's criterion (`brown-dadarlat-ext-trivial-class-gives-qd-extension`,
    BD Proposition 4.1) makes `∂(K_1(B)) ⊆ K_0(I_α)` singular.
  - By `type-i-qd-algebras-have-k0-embedding-property`, `I_α` has the
    K_0-embedding property.
  - By BD Proposition 4.6 (same import) it has the QD extension property.
  - `K⊗I_{α+1}` is the extension algebra `E(γ)` of its own Busby invariant
    `γ : K⊗B → Q(K⊗I_α)`, is stably finite, and `K⊗B` is separable, nuclear,
    QD and UCT.  So `K⊗I_{α+1}` is QD, and so is `I_{α+1}`.

So `E = I_β` is QD.  Only the singular subgroups `∂(K_1(I_{α+1}/I_α))` need to
be killed.  The single-algebra form is artifact §4, Corollary B.
