---
rg: 2
id: thompson-v-nonhyperlinearity-selects-stable-steinberg-branch
kind: route
title: Nonhyperlinearity of Thompson's V selects the HS-stable Steinberg branch
target: leavitt-steinberg-hs-stable
requires: [thompson-v-not-hyperlinear, leavitt-cylinder-swaps-generate-thompson-in-el, leavitt-gl-equals-el-and-perfect-unit-group, leavitt-steinberg-hs-stability-fork]
---

Put `L = L_(F_2)(1,2)`, `U = St_5(L)` and `Q = EL_4(L)`.

The cylinder-swap embedding of `leavitt-cylinder-swaps-generate-thompson-in-el`
places Thompson's `V` inside `L^x`. The four-leaf prefix code identifies `L`
with `M_4(L)`, so `L^x = GL_4(L)`, and `GL_4(L) = EL_4(L) = Q` by
`leavitt-gl-equals-el-and-perfect-unit-group`. Hyperlinearity passes to
subgroups, so if `V` is not hyperlinear then `Q` is not hyperlinear.

On the unstable branch of `leavitt-steinberg-hs-stability-fork`, `Q` is
hyperlinear. Exactly one branch holds, so `U` is normalized Hilbert--Schmidt
stable, which is the target.

## What this places on record

This is the same chain as `leavitt-kl-violation-selects-the-stable-steinberg-branch`,
entered from a different certificate. The KL lane certifies nonhyperlinearity
of the whole unit group by an algebraic identity; this lane asks for it on the
famous finitely presented simple subgroup `V`, where character rigidity
reduces it to one scalar ceiling (`thompson-v-one-word-strict-hs-ceiling`).
Read contrapositively, it bounds the unstable branch from below: any proof that
`U` is HS-unstable is also the first proof that Thompson's `V` is hyperlinear.
