---
rg: 2
id: k1-injectivity-extends-over-properly-infinite-quotients-proof
kind: route
title: Proof of the extension lemma for K1-injectivity via projection-realized exponential classes
target: k1-injectivity-extends-over-properly-infinite-quotients
requires: []
artifacts:
  - research/artifacts/lxi-halving-homotopy-and-extensions-2026-09-12.md
---

Artifact, Lemma 1.

1. Let `[u] = 0` in `K_1(A)`. Then `π(u) ∈ U_0(A/I)` by K1-injectivity of the quotient. Lift to
   `w ∈ U_0(A)` and put `y = uw^* ∈ U(Ĩ)`, so `[y] = 0` in `K_1(A)`.
2. Exactness gives `[y]_{K_1(I)} = δ_0(g)` for some `g ∈ K_0(A/I)`. Since `A/I` is properly infinite, `g = [e]`
   for a projection `e ∈ A/I` (Cuntz 1981).
3. With a self-adjoint lift `h` of `e` (sign adjusted), `y' = exp(2πih)` lies in `U(Ĩ) ∩ U_0(A)` and has
   `[y']_{K_1(I)} = δ_0([e])` (Rordam--Larsen--Laustsen 12.2.2).
4. `yy'^*` is K1-trivial in `Ĩ`, so it lies in `U_0(Ĩ) ⊆ U_0(A)`. Hence `u = (yy'^*) y' w ∈ U_0(A)`.
