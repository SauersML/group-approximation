---
rg: 2
id: universal-split-pair-seed-ring-proof
kind: route
title: Read the four properties off the binary-word model and the presentation
target: universal-split-pair-seed-ring
requires:
  - full-idempotent-ring-has-properly-infinite-unit
artifacts:
  - research/artifacts/universal-seed-review-2026-09-07.md
  - research/artifacts/universal-seed-model-test-2026-09-07.md
---

## Proof

**Nonzero, characteristic zero.**  Let `M` be the free abelian group on
finite binary words.  Define `s_i(w) = iw` and `t_i(iw) = w`, `t_i(jw) = 0`
for `j != i`, `t_i(empty) = 0`.  Then `t_is_j = delta_(ij)` as endomorphisms
of `M`, so the assignment factors through `C`, and the image contains the
identity acting as the identity on a free abelian group, so `1 != 0` in `C`
and no integer multiple of `1` vanishes.  In this model
`s_0t_0 + s_1t_1` is the projection killing the empty word, which is not the
identity, so the presentation really omits that relation.

**Finite generation.**  `C` is generated as a ring by four elements.  In
`EL_n(C)` with `n >= 3`, `e_(ij)(r)e_(ij)(r') = e_(ij)(r+r')` and
`[e_(ik)(r), e_(kj)(r')] = e_(ij)(rr')` for a third index `k`, so the
elementary matrices with coefficients `1, s_0, s_1, t_0, t_1` generate every
`e_(ij)(r)`, and those generate `EL_n(C)`.

**The witness.**  `t_0s_0 = 1` is a defining relation, and

```text
t_1 e s_1 = t_1 s_1 - (t_1 s_0) t_0 s_1 = 1 - 0 = 1,
```

so `1` lies in `C e C`.

**Universality.**  `C` is presented by the four relations `t_is_j = delta_(ij)`
and nothing else, so any quadruple `v_0,v_1,w_0,w_1` in a unital ring `R`
with `w_iv_j = delta_(ij)` determines a unital map `C -> R`.  By
`full-idempotent-ring-has-properly-infinite-unit`, every ring satisfying the
manuscript's hypothesis carries such a quadruple.
