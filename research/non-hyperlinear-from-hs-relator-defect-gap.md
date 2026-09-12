---
rg: 2
id: non-hyperlinear-from-hs-relator-defect-gap
kind: route
title: Linearize the normalized-HS relator gap and exclude canonical microstates
target: non-hyperlinear-group
requires:
  - saturated-group-hs-relator-defect-gap
  - defect-saturation-full-mf-radical
  - fixed-hs-word-gap-is-linear-domination
artifacts:
  - research/artifacts/hs-defect-gap-and-padding-2026-09-07.md
  - research/artifacts/hs-word-gap-linearization-2026-09-07.md
---

## Why sufficient

The prerequisites supply the explicit two-generated finitely presented group
`Q=<S|R>` and the constant `eta>0` of `(HSG)`.

The established linearization prerequisite turns this into the global
bound `D_2(U) <= (2/eta)d_2(U)` in every matrix dimension.

Suppose `Q` is hyperlinear.  Then `L(Q)` embeds in `R^omega`, so the
restriction of the trace to the canonical unitaries kills every nonidentity
element, and pulling the embedding back through matrix microstates gives
unitary tuples `U^((n)) in U(d_n)^S` with

```text
d_2(U^((n))) -> 0,
||U_s^((n)) - I||_2 -> sqrt 2   for each nontrivial generator s.
```

Since `Q` is infinite it is nontrivial, so at least one of its generators
is nontrivial. Identity generators, if present, have distance tending to
zero. Therefore `D_2(U^((n))) -> sqrt 2`, whereas the global linear
bound and `d_2(U^((n))) -> 0` force `D_2(U^((n))) -> 0`, a contradiction.

So `Q` is not hyperlinear, and it is explicit.

By `fixed-hs-word-gap-is-linear-domination`, the still-open (HSG)
prerequisite is equivalently a global bound `D_2 <= C d_2`.
The conversion is a proved reduction, not a source of the missing gap.
