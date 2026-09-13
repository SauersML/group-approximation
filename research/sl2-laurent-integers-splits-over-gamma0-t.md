---
rg: 2
id: sl2-laurent-integers-splits-over-gamma0-t
kind: claim
title: "SL_2(Z[t,t^-1]) is the amalgam of SL_2(Z[t]) and its diag(1,t)-conjugate over Gamma_0(t)"
---

Let `R = Z[t,t^{-1}]`, `A = SL_2(Z[t])`, `D = diag(1,t)` (an element of `GL_2(R)`), and

`Gamma_0(t) = { [[a,b],[c,d]] in SL_2(Z[t]) : c in tZ[t] }`.

Then

`SL_2(R) = A *_{Gamma_0(t)} D A D^{-1}`,

where `D A D^{-1} = { [[a,b],[c,d]] in SL_2(R) : a, d in Z[t], b in t^{-1}Z[t], c in tZ[t] }`
and `A ∩ D A D^{-1} = Gamma_0(t)`.

The same argument at the other end, with the tree of `Q((t^{-1}))`, gives
`SL_2(R) = SL_2(Z[t^{-1}]) *_{Gamma_0(t^{-1})} D^{-1} SL_2(Z[t^{-1}]) D`.

The mechanism: `SL_2(R)` acts on the Bruhat–Tits tree of `SL_2(Q((t)))` with an
edge as a fundamental domain, because the vertex stabilizer `SL_2(Z[t])` acts on the
neighbours of its vertex through `SL_2(Z)` acting on `P^1(Q)`, which is transitive.
Proof in `sl2-laurent-integers-splits-over-gamma0-t-proof`.

Novelty: this is the integral analogue of the classical decomposition of
`SL_2(k[t,t^{-1}])` over a field `k`, and it may well be folklore or in the
literature on `SL_2(Z[t,t^{-1}])` (Krstić–McCool; Bux–Wortman). This region has not
located a printed statement; the proof here is self-contained.

Consequence for Zaremsky Problem 3.3: `sl2-laurent-integers-fg-iff-gamma0-t-in-fg-subgroup`.
