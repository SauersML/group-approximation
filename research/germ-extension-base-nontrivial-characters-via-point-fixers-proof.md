---
rg: 2
id: germ-extension-base-nontrivial-characters-via-point-fixers-proof
kind: route
title: Meinert's criterion for G acting on the sublevel germ complex K_{<=m}, whose cube stabilizers are virtually conjugates of point-fixers of B
target: germ-extension-base-nontrivial-characters-via-point-fixers
requires:
  - germ-complex-and-bux-gonzalez-morse-inputs
  - meinert-cocompact-action-criterion
---

Items (K), (Stab), (Orb), (Conn) and (Fin) are those of `germ-complex-and-bux-gonzalez-morse-inputs`. Items (MMV),
(Mon), (FI) and (Conj) are those of `meinert-cocompact-action-criterion`. Hypotheses 1–3 and the point-fixer condition
are those of the claim.

**Paradigm note.** The Morse route (`germ-extension-base-trivial-characters-lie-in-sigma-proof`) needs a
`χ`-equivariant height on `K`. If `χ` is nonzero on a cell stabilizer, no such height exists, since `h(gy) = χ(g) + h(y)`
with `gy = y` forces `χ(g) = 0`. Here that obstruction is used as the input instead: Meinert's criterion asks for
exactly this nonvanishing.

## Step 1 (G has type F_m)

(Fin) with `n = m` applies by hypotheses 1–3.

## Step 2 (the complex)

Put `Y = K_{<=m}`.

- By (Conn) with `n = m >= 1`, `Y` is `(m−1)`-connected.
- By (Orb) with `n = m` and hypothesis 1, `G` has finitely many orbits of cubes in `Y`, so the action is cocompact.
- `Y` is a union of cubes on which `μ <= m`. So every vertex of a cube of `Y` has at most `m` hidden points.

## Step 3 (cube stabilizers)

Let `C` be a cube of `Y`, of dimension `j`, and put `S = Stab_G(C)`.

1. By (Stab), `S` has a finite-index subgroup `S_1 = g SingFix_G(M,M') g^{-1}` for some `g in G` and finite sets
   `M ⊆ M' ⊆ sing(G)`, where `|M'|` is the largest number of hidden points at a vertex of `C`. By Step 2, `|M'| <= m`.
2. By (Stab) and hypothesis 3, `Fix_B(M')` has finite index in `SingFix_G(M,M')`. So `S_2 = g Fix_B(M') g^{-1}` has
   finite index in `S`.
3. **Type.** `Fix_B(M')` has type `F_m` by hypothesis 2. So does its conjugate `S_2`, and so does `S`, which contains
   `S_2` with finite index. (A finite-index overgroup of a group of type `F_m` has type `F_m`. Belk–Hyde–Matucci use
   the same fact through Geoghegan, Proposition 7.2.3.) In particular `S` has type `F_{m−j}`.
4. **Nonvanishing.** `χ(g x g^{-1}) = χ(x)`, so `χ|_{S_2} != 0` because `χ|_{Fix_B(M')} != 0`. Hence `χ|_S != 0`.
5. **Invariant.** `[χ|_{Fix_B(M')}] in Σ^m(Fix_B(M'))` by hypothesis. By (Conj),
   `[χ|_{S_2}] in Σ^m(S_2)`. By (FI) for `S_2 <= S`, `[χ|_S] in Σ^m(S)`. By (Mon), `[χ|_S] in Σ^{m−j}(S)` for `j >= 1`.
   For `j = 0` this is the statement itself.

## Step 4 (Meinert's criterion)

Apply (MMV) to `G` acting on `Y`.

- `Y` is `(m−1)`-connected and the action is cocompact (Step 2).
- Every cube, of any dimension, has a stabilizer on which `χ` is nonzero (Step 3.4).
- Every cube of dimension `j < m` has a stabilizer of type `F_{m−j}` on which `χ` lies in `Σ^{m−j}` (Step 3.3 and 3.5).

So `[χ] in Σ^m(G)`. ∎

## Remarks

- Only `K_{<=m}` is used, not `K_{<=m+1}`. So hypotheses 1 and 2 are needed only for `m`-element sets. The base-trivial
  Morse theorem needs `m+1`, because it needs `Y` to be `m`-connected.
- The proof never uses that the `B`-orbits are infinite. Finite orbits are allowed.
