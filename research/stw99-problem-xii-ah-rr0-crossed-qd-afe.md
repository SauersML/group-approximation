---
rg: 2
id: stw99-problem-xii-ah-rr0-crossed-qd-afe
kind: claim
title: Quasidiagonal Z-crossed products of real rank zero AH algebras are AF-embeddable (STW Problem XII)
root: true
distinct_from:
  stw99-problem-xi-zd-crossed-stably-finite-qd: that varies the group (Z^d on commutative coefficients); this varies the coefficients (AH of real rank zero under a single automorphism), following Nate Brown's solved AF-coefficient case.
artifacts:
  - research/artifacts/stw99-xi-xii-dynamics-qd-2026-08-30.md
  - research/artifacts/stw12-periodic-action-af-embedding-audit-2026-08-30.md
  - research/artifacts/stw12-periodic-factor-decomposition-audit-2026-08-30.md
---

**Problem XII of Schafhauser--Tikuisis--White, arXiv:2506.10902.**  Let
`A` be an AH algebra of real rank zero and `α : Z ↷ A` with `A ⋊ Z`
quasidiagonal.  Is `A ⋊ Z` AF-embeddable?

Nate Brown (JFA 1998) solved the AF-coefficient case: for `A` AF, `A ⋊ Z`
is AF-embeddable ⟺ quasidiagonal ⟺ stably finite ⟺ an
incompressibility condition on the induced `K_0`-dynamics.  The problem
asks for the first step beyond AF coefficients.

## Attempts

The outer-periodic-action slice is now unconditional.
`stw12-periodic-actions-over-af-embeddable-algebras` proves that whenever an
AF-embeddable coefficient algebra satisfies `alpha^n=Ad(v)`, its integer
crossed product embeds into `M_n(A tensor C(T))` by a cyclic Floquet matrix
whose wrap-around entry is `vz`, and is therefore AF-embeddable.  Every AH
algebra is AF-embeddable, so this settles Problem XII for automorphisms of
finite order in `Out(A)` without assuming real rank zero or quasidiagonality.
Approximately inner powers, approximate periodicity, and the general
quasidiagonal case remain open here.

The AF proof runs through the ordered `K_0` dynamical incompressibility;
for AH of real rank zero, `K_0` (with its order and the `K_1`-graded
data) still governs much of the structure (real rank zero gives
projection-rich algebras), so the expected route is a
Brown-incompressibility criterion on `(K_0(A), K_0(A)_+, α_*)` plus the
Elliott-classification of the coefficients.  No general theorem beyond the
problem statement is recorded in the literature ingested here.

There is now an aperiodic decomposable slice beyond AF coefficients.
`stw12-periodic-factor-decomposable-actions-are-af-embeddable` treats

```text
A=B tensor C,        alpha=beta tensor gamma,
```

where `B` is AF, `C` is AF-embeddable, and `gamma` is outer-periodic, while
`beta` is arbitrary.  The diagonal crossed product embeds in the tensor
product of the two factor crossed products.  Stable finiteness of the
diagonal algebra detects `B rtimes_beta Z`; Brown embeds this first factor
in AF, and the outer-periodic Floquet theorem embeds the second.  If `C` is
real-rank-zero AH, then so is `B tensor C`.  Taking `C` to be an irrational
rotation algebra and `beta` to be the bilateral CAR shift gives a non-AF
coefficient and an outer-aperiodic automorphism, so this is outside both
previous positive classes.
