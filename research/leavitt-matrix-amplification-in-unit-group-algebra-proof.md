---
rg: 2
id: leavitt-matrix-amplification-in-unit-group-algebra-proof
kind: route
title: Scalars commute with constants, and the constant corner is two by two
target: leavitt-matrix-amplification-in-unit-group-algebra
requires: [leavitt-corner-idempotent-unital-surjection]
artifacts:
  - research/artifacts/leavitt-stable-finiteness-audit-2026-08-17.md
  - research/artifacts/verify-s3-corner-2026-08-17.py
  - GroupApproximation/Leavitt/LeavittSelfSimilarity.lean
  - GroupApproximation/Leavitt/LeavittDiagonalClass.lean
---

## Direct proof

Write `Theta_2 : M_2(R) -> R`, `Theta_2((a_ij)) = sum_ij s_i a_ij t_j`, for the
binary self-similarity isomorphism (`LeavittFamily.binaryMatrixRingEquiv`),
with inverse `Phi(r)_ij = t_i r s_j`.

**Step 1 — the prerequisite's units are the constant matrices.**  With
`x = s_0t_1`, `y = s_1t_0`, `u = 1+x`, `v = 1+y`, `g = uv` as in
`leavitt-corner-idempotent-unital-surjection`, and using
`s_0t_0 + s_1t_1 = 1`,

    u = Theta_2 [[1,1],[0,1]],   v = Theta_2 [[1,0],[1,1]],
    g = Theta_2 [[0,1],[1,1]],   uvu = Theta_2 [[0,1],[1,0]] = x + y.

So `H = <u,v> = Theta_2(GL_2(F_2)) ~= S_3`, of order exactly six; distinctness
of the six is `Phi(r)_ij = t_i r s_j` applied entrywise.

**Step 2 — the finite corner.**  In `F_2[H]`, put

    f_11 = [1]+[u]+[v]+[g],      f_12 = [v]+[w]+[g]+[g^2],
    f_21 = [u]+[w]+[g]+[g^2],    f_22 = [1]+[u]+[v]+[g^2],

`w = uvu`.  Then `f_ij f_kl = delta_jk f_il` for all sixteen index pairs,
`f_11 + f_22 = e`, and `e F_2[H] e` has exactly sixteen elements, equal to the
span of the four `f_ij`.  Hence `e F_2[H] e ~= M_2(F_2)`.

This is a computation in a six-element group algebra and uses **no** Leavitt
relation; it is replayed exactly by
`research/artifacts/verify-s3-corner-2026-08-17.py` (run on MSI 2026-08-17,
all assertions pass).  Conceptually it is `F_2[C_3] = F_2 x F_4` with `e`
cutting out `F_4`, and `e F_2[S_3] e` the split crossed product of `F_4` by
its Galois group.

**Step 3 — a commuting scalar copy of `G`.**  `delta(q) = Theta_2(q I_2)`
(`LeavittFamily.crossUnit`, with inverse `s_0 q^-1 t_0 + s_1 q^-1 t_1`) is an
injective group endomorphism of `G`, because `Theta_2` is a ring isomorphism.
Scalar matrices commute with constant matrices, so `delta(G)` centralizes `H`.
If `q I_2 = C` with `C` constant invertible then `C`'s off-diagonal entries
vanish and both diagonal entries equal `q`, so `C = lambda I_2` with
`lambda in F_2^x = {1}`; hence `delta(G) n H = 1` and

    delta(G) x H  ->  G

is an injective group homomorphism.  Passing to group algebras,
`S (x)_(F_2) F_2[H] ~= F_2[delta(G) x H] -> S` injectively.

**Step 4 — cut and conclude at `N = 2`.**  `e` lies in the second tensor
factor, so it commutes with the image of `S`, and

    M_2(S) ~= S (x) M_2(F_2) ~= S (x) e F_2[H] e  ->  e S e

is an injective ring map `j_2` with `j_2(I_2) = e`.  This shows only that its
image is a subring of `eSe`; no surjectivity onto `eSe` follows from the
tensor-factor construction.

**Step 5 — induction.**  Given an injective ring map `j : M_2(S) -> S` with
`j(I_2)` idempotent, `M_2(j) : M_4(S) = M_2(M_2(S)) -> M_2(S)` is injective
and carries `I_4` to `j(I_2) I_2`, an idempotent of `M_2(S)`.  So
`j . M_2(j) : M_4(S) -> S` is injective and carries `I_4` to an idempotent of
`S`.  Iterating gives `j_N` for every `N = 2^k`, with
`E_N = j_N(I_N)` idempotent and image contained in `E_N S E_N`.

## Note on the source's version

The source builds `j_N` in one step, from the tensor-power representation
`H^k -> GL_(2^k)(F_2)` (faithful, since a pure tensor of invertible matrices
is the identity only if each factor is scalar and `F_2` has only one nonzero
scalar), the length-`k` prefix-code self-similarity `Theta_N`, and
`E_k = e^(x k)` with `E_k F_2[H^k] E_k ~= M_(2^k)(F_2)`.  That is correct and
equivalent; the induction above is recorded instead because it needs only the
single finite certificate of Step 2 and no prefix-code bookkeeping.
