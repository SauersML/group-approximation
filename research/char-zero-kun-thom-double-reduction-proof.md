---
rg: 2
id: char-zero-kun-thom-double-reduction-proof
kind: route
title: Verify the Kun--Thom hypotheses for the characteristic-zero pair, pass to the preimage of the torsion-free actor, and split off the free quotient of its graph of groups
target: char-zero-kun-thom-double-reduces-nonsofic-atiyah-to-edge
requires:
  - kun-thom-actor-strong-atiyah-via-formal-torus
  - char-zero-kun-thom-actor-has-torsion-free-finite-index-subgroup
  - kt-pair-group-double-is-nonsofic
  - strong-atiyah-passes-to-locally-indicable-extensions
artifacts:
  - experiments/kun-thom-formal-torus-2026-09-17/check_formal_torus.py
---

Notation is as in [[char-zero-kun-thom-double-reduces-nonsofic-atiyah-to-edge]]:
`r, d >= 3`, `p >= 3`, `R = Z[x^(+-1)]`, `P = Z[x_1,...,x_d]`,
`G_0 = EL_r(R) semidirect SL_d(Z)`, `Gamma = EL_r(P)`, `H = K semidirect Gamma_d(p)`.
Elements of `G_0` are pairs `(M, A)` with `(M,A)(M',A') = (M alpha_A(M'), AA')`.
We write `e_ij(f)` for an elementary matrix, `(g, I)` as `g`, and `(I, A)` as `A`,
so that `A g A^-1 = alpha_A(g)`.

## Step 1: `Gamma` is infranormal and not normal

Recall the definition from [[kt-pair-group-double-is-nonsofic]]: `Gamma` is
infranormal in `G_0` when `P_Gamma = { g : g Gamma g^-1 <= Gamma }` generates `G_0`.

* **`Gamma` lies in `P_Gamma`.** This is clear.
* **Nonnegative substitutions lie in `P_Gamma`.** Let `A in SL_d(Z)` have
  nonnegative entries. Then `A v >= 0` whenever `v >= 0`, so `alpha_A(P) <= P`,
  and `A Gamma A^-1 = alpha_A(Gamma) <= Gamma`. The matrices `I + E_ij`
  (`i != j`) are nonnegative. They generate `SL_d(Z)`, because their inverses
  `I - E_ij` lie in the generated group. So `<P_Gamma>` contains `SL_d(Z)`.
* **Every elementary generator of `EL_r(R)` lies in `<P_Gamma>`.** Take
  `e_ij(x^v)` with `v in Z^d` and `v != 0`. Write `v = k v'` with `k >= 1` and
  `v'` primitive. Choose `B in SL_d(Z)` with `B v' = e_1`; it exists because
  `SL_d(Z)` acts transitively on primitive vectors. Then
  `B e_ij(x^v) B^-1 = e_ij(x^(Bv)) = e_ij(x_1^k)`, which lies in `Gamma`. So
  `e_ij(x^v) = B^-1 e_ij(x_1^k) B` lies in `<P_Gamma>`. The elements
  `e_ij(+- x^v)` generate `EL_r(R)`, and `<P_Gamma> = G_0`.
* **`Gamma` is not normal.** Let `A = I - E_12`. It sends `e_2` to `e_2 - e_1`,
  so `alpha_A(x_2) = x_1^-1 x_2`. Hence
  `A e_12(x_2) A^-1 = e_12(x_1^-1 x_2)`. Its off-diagonal entry is not a
  polynomial, while every element of `EL_r(P)` has polynomial entries.

Check 7 of the script tests compression and non-normality.

## Step 2: property (T) and nonsoficity of `D`

* `EL_r(S)` has property (T) for every finitely generated commutative ring `S`
  and every `r >= 3`, by Ershov--Jaikin-Zapirain. This is the program's Kazhdan
  input, see [[el-r-polynomial-robust-spectral-gap]]. It applies to `S = P` and to
  `S = R`.
* `SL_d(Z)` has (T) for `d >= 3`, and (T) passes to extensions. So `G_0` has
  (T).

Kun--Thom Theorem A, version 3, as recorded in [[kt-pair-group-double-is-nonsofic]],
then gives: `D = G_0 *_Gamma G_0` is not sofic.

## Step 3: the finite-index subgroup `D_H`

* **`H` is normal of finite index in `G_0`.** Let `ev : G_0 -> GL_r(F_p) x SL_d(F_p)`
  send `(M, A)` to `(M(1) mod p, A mod p)`. It is a homomorphism, because
  `alpha_A(M)(1) = M(1)`. Its kernel is `H`. Its image is
  `SL_r(F_p) x SL_d(F_p)`, since elementary matrices over `F_p` generate
  `SL_r(F_p)`. So `[G_0 : H] = |SL_r(F_p)| |SL_d(F_p)|`.
* **The fold.** Let `f : D -> G_0` be the identity on both factors. Then
  `D_H = f^-1(H)` is normal in `D` with `D/D_H = G_0/H` finite.
* **Nonsoficity.** A group with a sofic finite-index subgroup is sofic. So
  `D_H` is not sofic.
* **The split extension.** `f` restricts to an isomorphism on the first factor
  `G_0`, so `f|_(D_H)` is split by `H <= G_0`, and `D_H = F semidirect H` with
  `F = ker f`.

## Step 4: `F` is free and `D_H` is torsion-free

Let `T` be the Bass--Serre tree of `D`. Its vertex stabilizers are conjugates
of the two factors, and its edge stabilizers are conjugates of `Gamma`.

* **`F` is free.** `F` is normal and `f` is injective on each factor, so
  `F cap g G_0 g^-1 = g (F cap G_0) g^-1 = 1`. Hence `F` acts freely on `T` and
  is free.
* **`D_H` is torsion-free.** A finite subgroup of `D` fixes a vertex of `T`, so
  it lies in some `g G_0 g^-1`. Then it lies in
  `D_H cap g G_0 g^-1 = g (D_H cap G_0) g^-1 = g H g^-1`. That group is
  torsion-free by [[char-zero-kun-thom-actor-has-torsion-free-finite-index-subgroup]].

## Step 5: the quotient graph of groups

`D_H` acts on `T`. The quotient graph and its stabilizers are as follows.

* **Vertices.** Both vertex orbits of `D` split into
  `D_H \ D / G_0 = (D/D_H)/f(G_0)` orbits. This is a single point, because
  `f(G_0) = G_0` maps onto `G_0/H`. So there are two vertices, with stabilizers
  `D_H cap G_0 = H`.
* **Edges.** The edge orbits are `D_H \ D / Gamma = G_0 / (H Gamma)`. Now
  `ev(Gamma) = SL_r(F_p) x 1`, so `H Gamma = ev^-1(SL_r(F_p) x 1)`. Its index is
  `m = |SL_d(F_p)|`.
* **Edge groups.** Take representatives `A_1, ..., A_m in SL_d(Z)` for
  `SL_d(F_p)`. The edge stabilizers are the groups
  `D_H cap A_k Gamma A_k^-1 = H cap EL_r(alpha_(A_k)(P))`. Each has finite index
  in the (T) group `alpha_(A_k)(Gamma)`, so it is infinite and has (T).
* **Strong Atiyah on the pieces.** Every vertex and edge group is a subgroup of
  a conjugate of `H`. So each satisfies Strong Atiyah over `C`, by
  [[kun-thom-actor-strong-atiyah-via-formal-torus]].

This proves items 1-3 of the claim.

## Step 6: the dichotomy

* **If `D_H` satisfies Strong Atiyah over `C`.** Then `D_H` is a nonsofic group
  satisfying Strong Atiyah, which is `nonsofic-group-satisfying-strong-atiyah`.
* **If it does not.** Then `D_H` is a torsion-free counterexample to
  `strong-atiyah-torsion-free`.
* **Where a witness lives.** A witness matrix is not supported in any vertex
  group. Vertex groups satisfy Strong Atiyah, and the rank does not change under
  induction.

This proves item 4.

## Step 7: the reduction to Kazhdan-edge permanence

Assume `strong-atiyah-kazhdan-edge-amalgam-permanence` over `C`.

* **The free quotient.** The underlying graph `Y` has 2 vertices and `m` edges,
  so `pi_1(Y) = F_(m-1)`. Collapsing all vertex groups gives a surjection
  `q : D_H -> F_(m-1)`. Its kernel `N` acts on `T` with quotient the universal
  covering tree `Ytilde`, and with the same vertex and edge stabilizers. So `N`
  is the fundamental group of a tree of groups over `Ytilde`. Its vertex groups
  are conjugates of `H`, and its edge groups are conjugates of the Step 5 edge
  groups.
* **Finite subtrees.** Let `S` be a finite subtree of `Ytilde`, and remove one
  leaf. Then `pi_1(S) = pi_1(S - leaf) *_E H'`, where `E` is an infinite (T)
  edge group satisfying Strong Atiyah and `H'` is a conjugate of `H`.
  - All groups involved are subgroups of the torsion-free group `D_H`.
  - By induction on the number of vertices, `pi_1(S - leaf)` satisfies Strong
    Atiyah over `C`.
  - The assumed permanence then gives Strong Atiyah for `pi_1(S)`.
* **Directed union.** `N` is the directed union of the subgroups `pi_1(S)`.
  They embed, because a subtree of groups injects into the tree of groups.
  Every finite matrix over `C[N]` has entries in some `C[pi_1(S)]`. The von
  Neumann rank does not change under induction to an overgroup. So `N` satisfies
  Strong Atiyah over `C`, with integer ranks.
* **The extension.** `N` is torsion-free and normal in `D_H`, and
  `D_H / N = F_(m-1)` is locally indicable. By
  [[strong-atiyah-passes-to-locally-indicable-extensions]] (Jaikin-Zapirain--Lopez-Alvarez,
  Proposition 6.5), `D_H` satisfies Strong Atiyah over `C`.

With Steps 3 and 6, this proves item 5. Only finitely many amalgam steps, all
over edge groups of `N`, are used.

## Why the known permanence routes stop

* **Approximation.** Sofic groups are closed under residual soficity. So a
  residual normal chain of `D_H` with sofic quotients would make `D_H` sofic,
  contradicting Step 3.
* **The split extension.** In `D_H = F semidirect H`, the kernel `F` is free and
  satisfies Strong Atiyah. The quotient `H` is infinite with (T), so it is not
  locally indicable, and Proposition 6.5 does not apply.
* **Graph-of-groups permanence.** The known permanence for graphs of groups
  needs finite edge groups. The edges here are infinite (T), as
  recorded in [[atiyah-kazhdan-edge-blocks-both-permanence-routes]].
