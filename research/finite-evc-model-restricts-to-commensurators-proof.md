---
rg: 2
id: finite-evc-model-restricts-to-commensurators-proof
kind: route
title: Stabilizers commensurable with C cut out a finite commensurator model
target: finite-evc-model-restricts-to-commensurators
requires: []
artifacts:
  - research/artifacts/finite-evc-commensurator-restriction-2026-09-16.md
---

Full proof: Theorem 1 of `research/artifacts/finite-evc-commensurator-restriction-2026-09-16.md`.
Every cell stabilizer `G_σ` of `X` is virtually cyclic, because `X^{G_σ}` is nonempty. An
infinite subgroup of an infinite virtually cyclic group has finite index, so `~` is a
conjugation-invariant equivalence relation.

1. **Subcomplex.** Points of one open cell share a stabilizer. If `y` lies in the closure of a
   cell `σ` with `G_σ ~ C`, then `G_y ⊇ G_σ` is virtually cyclic, so `G_y ~ C`.
2. **Isotropy.** For `n` in `N`, `G_{nx} = nG_xn^{-1} ~ C`, so `Y_C` is `N`-invariant. For `x` in
   `Y_C` and `g` in `G_x`, `gCg^{-1} ~ gG_xg^{-1} = G_x ~ C`, so `N_x = G_x` is in `G[C]`.
3. **Finiteness.** If `gσ` and `g'σ` both lie in `Y_C`, then with `h = g'g^{-1}` we get
   `hCh^{-1} ~ h(gG_σg^{-1})h^{-1} = g'G_σg'^{-1} ~ C`. So `h` is in `N`, and each `G`-orbit of
   cells contributes at most one `N`-orbit.
4. **Fixed sets.**
   - `H <= N` not in `G[C]`: `H` is infinite. If `H` fixes `x` in `Y_C`, then `H ~ G_x ~ C`, a
     contradiction. So `Y_C^H` is empty.
   - Infinite `H` in `G[C]`: every `x` in `X^H` has `G_x ~ H ~ C`, so `Y_C^H = X^H`, which is
     contractible.
   - Finite `H <= N`: `Y_C^H` is the union of the contractible `X^D` over virtually cyclic
     `D ⊇ H` with `D ~ C`. This system is closed under finite intersections, and
     `X^D ∪ X^{D'} ⊆ X^{D∩D'}`. So every compact subset lies in one `X^D`, and all homotopy
     groups vanish. The union is nonempty: with `C_0` infinite cyclic of finite index in `C`,
     `E = ∩_{h in H} hC_0h^{-1}` is infinite cyclic, `~ C` and normalized by `H`, and
     `D = HE` qualifies. By Whitehead, `Y_C^H` is contractible.
5. **Consequences.**
   - `N` has type `F_infinity`. By step 4, `Y_C` is a finite model for `E_{G[C]} N`. A
     virtually cyclic group `V` has a finite-type `EV`: apply Lück–Weiermann,
     arXiv:math/0702646, Proposition 5.1(ii) in its "finite type" form to `TR ⊆ FIN` on `V`.
     This uses the finite 1-dimensional `E_FIN V` and the bar-construction `EF` for finite `F`.
     The same proposition applied to `TR ⊆ G[C]` on `N` then gives a finite-type `EN`. This is
     artifact item (F1'), which replaces an earlier appeal to Brown's criterion whose numbering
     was not verified.
   - Lück–Weiermann, arXiv:math/0702646, Proposition 5.1(ii) applies to `FIN <= G[C]`, because
     virtually cyclic groups have finite `E_FIN` models. It gives a finite `E_FIN N`.
   - `Δ_C` is a homomorphism because the generalized index is multiplicative and conjugation
     invariant. Its image is a finitely generated subgroup of the free abelian group
     `Q_{>0}^×`, so if nontrivial it surjects onto `Z`.
