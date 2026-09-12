---
rg: 2
id: kazhdan-kernel-quotient-rf-or-nonhyperlinear-proof
kind: route
title: Transport stability to the quotient, then apply Malcev residual finiteness
target: flexibly-hs-stable-kazhdan-kernel-quotient-rf-or-nonhyperlinear
requires: [flexible-hs-stability-passes-to-kazhdan-kernel-quotients, hyperlinear-flexibly-hs-stable-group-is-residually-finite]
---

## Direct proof

1. By `flexible-hs-stability-passes-to-kazhdan-kernel-quotients`, `Q = Γ/N` is
   flexibly HS stable. It is finitely generated because `Γ` is.
2. If `Q` is hyperlinear, `hyperlinear-flexibly-hs-stable-group-is-residually-finite`
   makes `Q` residually finite.
3. An infinite residually finite group has a nontrivial finite quotient, and so a
   nontrivial finite-dimensional unitary representation. So an infinite minimally
   almost periodic `Q` is not residually finite, and by step 2 it is not
   hyperlinear. ∎
