---
rg: 2
id: matrix-lamp-wreath-algebras-are-stably-finite
kind: claim
title: Matrix-lamp wreath algebras over a stably finite base group algebra are stably finite
distinct_from:
  rf-lamps-preserve-stable-finiteness-for-arbitrary-actions: that proves the statement for lamp algebras k[A] with A residually finite, which carry characters; here the lamp algebra is the simple infinite tensor power of M_2(k), which has no finite-dimensional representation.
  residual-lamp-quotients-handle-monomial-actions: that allows lamp-group automorphism twists; the commutative form of this algebra twists coordinates by characters (flips), outside that theorem.
  kun-thom-wreath-stably-finite: that is stable finiteness of the untwisted Kun--Thom wreath algebras, which embed here as the s-lamp subalgebra; this asks for the whole matrix-lamp crossed product.
artifacts:
  - research/artifacts/clifford-skew-ring-matrix-lamp-wreath-2026-09-12.md
---

**OPEN.** Let `k` be a field, `G` a group with `k[G]` stably finite, and `X` a `G`-set. Then the matrix-lamp
wreath

```text
B_X = (restricted tensor_X M_2(k)) semidirect G  =  C_lc({+-1}^X, k) semidirect (F_2 wr_X G)
```

is stably finite. The second form assumes `char k != 2`, and there the lamps flip coordinates.

This is the noncommutative analogue of (DWI1) in `rf-lamps-preserve-stable-finiteness-for-arbitrary-actions`.
For the Kun--Thom pair it decides the linear case of every oriented Clifford cover at once, through
`oriented-clifford-skew-rings-embed-in-matrix-lamp-wreath`.

## Attempts

- **Sofic extension: true.**
  - `B_X` is the anti-central factor of `k[H_X semidirect G]`, where `H_X` is the central product of copies
    of `D_8` over `X`, and `(1 +- z)/2` split it off.
  - When `H_X semidirect G` is sofic, for example when `G` is amenable (sofic-by-amenable is sofic), its group
    algebra is stably finite (`linear-sofic-group-algebra-is-stably-finite`), and so is `B_X`.
  - So a counterexample needs an action whose extension is nonsofic, as for the Kun--Thom pair.
  - **Correction (w4-vf-linear-b, 2026-09-12).** An earlier version said "when `G` is sofic, `H_X semidirect G`
    is amenable-by-sofic, hence sofic". That implication is false. The Kun--Thom wreath `F_2 wr_X G` has
    abelian lamps and a residually finite base, and it is not sofic. It sits inside `(H_X/Z) semidirect G`,
    and the false step would have settled this open claim for the Kun--Thom pair.
    (`research/artifacts/gk-vf-linear-b-verification-2026-09-12.md`, Section 14.)
- **Marked-site induction: dies at the first step.**
  - That proof separates `k[W]` by maps into `(C^(tensor r)) semidirect G`, using evaluation at infinity,
    which is a character of the lamp algebra.
  - `tensor_X M_2(k)` is simple and infinite-dimensional, so it has no unital map to any algebra with a
    finite-dimensional representation (artifact Section 2). None of those targets receives `B_X`.
- **Monomial theorem: does not apply.** Its twists fix the trivial character, and flips fix no point
  (artifact Remark 1.5).
- **Rank models: gated.**
  - `B_X` contains `k[F_2 wr_X G]` as the `s`-lamp subalgebra. A faithful rank-ultraproduct embedding of
    `B_X` makes the Kun--Thom wreath `k`-linear sofic, which is open over every field
    (`kun-thom-wreath-linear-sofic` over `C`).
  - The obvious tensor model fails even when the action is sofic. A permutation defect on a `delta`-fraction
    of `n` sites is implemented on `tensor M_2` by operators whose rank distance tends to `1` as `delta n`
    grows. That is the spinor obstruction of the Clifford cover artifact, Section 4.2.
- **Traces.** The normalized trace of `P_X` is invariant, and gives an `F_p`-valued trace on `B_X`. A defect
  has trace `0`. This constrains witnesses without forbidding them.
