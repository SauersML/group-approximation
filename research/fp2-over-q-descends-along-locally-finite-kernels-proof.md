---
rg: 2
id: fp2-over-q-descends-along-locally-finite-kernels-proof
kind: route
title: Averaging idempotents make rational coinvariants over a locally finite group exact, and exact coinvariants carry a partial free resolution to the quotient
target: fp2-over-q-descends-along-locally-finite-kernels
requires: []
---

Notation. For a finite subgroup `F`, put `e_F = |F|^(-1) sum_(f in F) f`. Then
`e_F f = f e_F = e_F` for `f in F`, `e_F^2 = e_F`, and `e_F b = aug(b) e_F` for
`b in Q[F]`, where `aug` is the augmentation.

**Step 1: the description of `I_L M`.**
- If `e_F m = 0` for a finite `F <= L`, then
  `m = (1 - e_F) m = sum_(f in F) |F|^(-1) (1 - f) m`, which lies in `I_L M`.
- Conversely, an element of `I_L M` is a finite sum `sum_j b_j m_j` with
  `b_j in I_L`. The finitely many elements in the supports of the `b_j`
  generate a finite subgroup `F <= L`, because `L` is locally finite. Then
  `e_F b_j = aug(b_j) e_F = 0`, so `e_F sum_j b_j m_j = 0`.

**Step 2: exactness of `M -> M_L`.** The functor is `Q (x)_(Q[L]) -`, so it is
right exact. Let `M' <= M` be a submodule and `x in M'` with `x in I_L M`. By
Step 1 there is a finite `F` with `e_F x = 0` in `M`, hence in `M'`, so
`x in I_L M'`. So `M'_L -> M_L` is injective, and the functor is exact.

**Step 3: descent of `FP_2`.** Let
`P_2 -> P_1 -> P_0 -> Q -> 0` be exact, with each `P_i` a finitely generated
free left `Q[G]`-module. Apply `M -> M_L`, using the `Q[L]`-structure.
- Since `L` is normal, `g I_L M = (g I_L g^(-1)) g M = I_L M`, so `M_L` is a
  left `Q[G/L]`-module and the maps stay `Q[G/L]`-linear.
- `Q[G]` is free as a left `Q[L]`-module on right coset representatives, so
  `Q[G]_L = Q[G]/I_L Q[G] = Q[G/L]`. So each `(P_i)_L` is a finitely generated
  free `Q[G/L]`-module.
- `Q_L = Q`, because `L` acts trivially on `Q`.
- By Step 2 the sequence `(P_2)_L -> (P_1)_L -> (P_0)_L -> Q -> 0` is exact.

So `G/L` is of type `FP_2` over `Q`.

**Step 4: finitely presented groups.** Let `X` be the presentation 2-complex
of a finite presentation of `G`, and `X~` its universal cover. The cellular
chain complex `C_2(X~) -> C_1(X~) -> C_0(X~) -> Z -> 0` consists of finitely
generated free `Z[G]`-modules, and it is exact because `X~` is connected and
simply connected. Tensoring over `Z` with `Q`, which is flat over `Z`, gives a
partial free resolution of `Q` over `Q[G]` of the required kind. `∎`
