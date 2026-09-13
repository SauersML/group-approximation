---
rg: 2
id: elementary-groups-over-polynomial-s-integers-are-fp
kind: claim
title: E_n(Z[1/m][t_1..t_k]) is finitely presented for n >= k+4
distinct_from:
  steinberg-finite-presentation-and-kazhdan-theorem: that is Krstić–McCool's finite presentation of the Steinberg group St_n(R) with property (T), and it draws no conclusion for EL_n(R); this controls the kernel K_2(n,R) for polynomial rings over Z[1/m] in the stable range, so the elementary group itself is finitely presented.
artifacts:
  - research/artifacts/bh-sl3-zt-host-2026-09-12.md
---

**ESTABLISHED (2026-09-12)** through
`elementary-groups-over-polynomial-s-integers-are-fp-proof`. It imports K-theory
from textbooks, as listed in the route. ~~Not independently reviewed.~~
*Reviewed (lane `bh-poly-linear-review`, 2026-09-12).* The argument is sound. The
review corrected the homotopy-invariance citation in the route and added a primary
source for the Steinberg import.

**Statement.** Let `m >= 1`, `k >= 0`, `A = Z[1/m]`, `R = A[t_1,...,t_k]` and
`n >= k+4`. Then `E_n(R)` is finitely presented.

**Special case.** `E_5(Z[t])` is finitely presented, with
`K_2(5, Z[t]) = K_2(Z) = Z/2`.

**Compare.**
- Krstić–McCool: `SL_3(Z[t])` is not finitely presented.
- Bux–Mohammadi–Wortman, arXiv:0801.1332, Thm 1: `SL_n(Z[t])` is not of type
  `FP_(n-1)`.

Neither excludes finite presentation for `n >= 5`. This statement is very likely
known to experts. No novelty is claimed.

**Prior art (review lane `bh-poly-linear-review`, 2026-09-12): KNOWN.** It
follows from U. Rehmann and C. Soulé, *Finitely presented groups of matrices*,
LNM 551 (1976).
- **Theorem I.** Let `A` be a finitely generated commutative ring of Krull
  dimension `d`, with `K_1(A)` and `K_2(A)` finitely generated, and let `n >= d+3`.
  Then `GL_n(A)` is finitely presented.
- **§2.** For `n >= d+3`, the maps `GL_n(A)/E_n(A) -> K_1(A)` and
  `Ker(St_n(A) -> E_n(A)) -> K_2(A)` are isomorphisms. They cite Bass, and
  Dennis, Stein and van der Kallen. With a lemma on extensions, they reduce
  Theorem I to the finite presentation of `St_n(A)`.
- **Theorem 2.** For `A` as in Theorem I and `Φ` of rank at least 3, `St(Φ,A)` is
  finitely presented.
- **Consequence.** `E_n(A) = St_n(A)/K_2(n,A)` is finitely presented, since
  `K_2(n,A)` is finitely generated.
- **Scope.** Their remark says that if a regular ring satisfies the hypotheses,
  so do `A[t]` and `A[t,t^-1]`.
  - `Z[1/m]` is regular, and its `K_1` and `K_2` are finitely generated (the
    K-theory imports of the route).
  - So `R = Z[1/m][t_1..t_k]` qualifies, with `d = k+1`.
- Read from the scanned LNM pages 164–165.
