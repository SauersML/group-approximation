---
rg: 2
id: leavitt-unit-microstates-are-asymptotically-primitive
kind: claim
title: Hilbert--Schmidt microstates of the binary Leavitt unit group are asymptotically primitive
distinct_from:
  leavitt-units-admit-no-bounded-block-monomial-hs-model: that is the ultraproduct statement for exactly block-monomial models; this is the finitary statement for arbitrary almost-multiplicative unitary maps and approximately invariant equal-rank decompositions of any rank, with no trace hypothesis.
  leavitt-regular-atlas-block-monomial-gap: that bounds specific A8-atlas transports over a fixed index set; this concerns every microstate and every approximately invariant decomposition.
artifacts:
  - research/artifacts/ex-q34-imprimitivity-witness-2026-09-12.md
---

**ESTABLISHED.**  Let `R = L_(F_2)(1,2)`.  For every finite `E ⊆ R^x` and
`eps > 0` there are a finite `F ⊆ R^x` and `delta > 0` with the following
property.  Let `U : F -> U(d)` be any `(F, delta)`-almost multiplicative map
(any `d`, no trace condition).  Let `C^d = ⊕_(i<=n) V_i` be any orthogonal
decomposition into subspaces of equal dimension `k` (any `k`) with
`def_B(U_x) <= delta` for `x in F`.  Then every `g in E` maps all but an
`eps`-fraction of the blocks `V_i` into themselves, up to the
`2 sqrt(3) delta` error of `coarse-frame-normalizers-are-near-block-monomial`.

In Mackey's language: no HS microstate of `R^x` is approximately induced with a
nontrivial induction skeleton.  Every approximate system of imprimitivity is
asymptotically fixed.  Any construction proving
`binary-leavitt-unit-group-hyperlinear` must therefore be asymptotically
primitive at every scale, for every rank of decomposition.  This is a
checkable necessary condition on candidate models.  With a regular trace and
bounded `k` it forces the contradiction of
`leavitt-units-admit-no-bounded-block-monomial-hs-model`.

## Attempts

Established; see `leavitt-unit-microstates-asymptotically-primitive-proof`.
