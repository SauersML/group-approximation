---
rg: 2
id: deligne-homogeneous-bundle-models-die-at-lattice-residual
kind: claim
title: No Lie-homogeneous circle-bundle model of Deligne's triple cover exists over a lattice quotient of Sp_4(R), because lifting the lattice into the circle extension would make its three- or six-fold cover residually finite, against Deligne's residual
distinct_from:
  deligne-third-floor-failure-is-continuous-untwisting: that rewrites floor failure as a finitely approximable space with a continuous untwisting and kills discrete-phase, Bernoulli-profinite and local-rule spaces; this kills the Lie-homogeneous spaces Sp_4(R)/Lambda_0 with their algebraic circle bundles, a class that node does not treat, and it does so by non-existence, without using finite approximability.
  deligne-covers-of-sp2g-z-have-finite-residual-2z: that is Deligne's residual for Sp_2g(Z) itself and is an input here; this transfers it to every lattice of Sp_4(R) that could carry a homogeneous untwisting, unconditionally for the commensurability class of Sp_4(Z) and under the congruence subgroup property for the other lattices.
  central-extension-untwisting-over-boundaries: that obstructs realizing a finite central extension over boundary actions through point stabilizers; this concerns finite-volume homogeneous spaces, where all stabilizers are trivial, and the obstruction sits in the residual of a different lattice, not in a stabilizer.
  deligne-universal-cover-lattice-is-non-rf-kazhdan: that records non-residual-finiteness of the preimage of Sp_2n(Z); this proves that a homogeneous untwisting would force residual finiteness of the preimage of the lattice Lambda_0 that defines the space.
---

**ESTABLISHED** (`deligne-homogeneous-bundle-models-die-at-lattice-residual-proof`), with part (b) stated under
the congruence subgroup property as an explicit hypothesis. Unreviewed.

## Setting

- `G = Sp_4(R)`, `p : G~ -> G` its universal cover, `z` a generator of `K_0 = ker p`, which is infinite cyclic.
- `Gamma = Sp_4(Z)`, `Gamma~ = p^(-1)(Gamma)`, `E_3 = Gamma~ / <z^3>`, as in the rest of the graph.
- For a subgroup `Lambda_0 <= G`: `Lambda_0~ = p^(-1)(Lambda_0)` and `Lambda_(0,n) = Lambda_0~ / <z^n>`. The latter
  is the preimage of `Lambda_0` in the connected `n`-fold cover `G_n = G~ / <z^n>`.
- `T = R/Z`. For `t in T` put
  ```text
  L_t = (G~ x T) / { (z^k, -k t) : k in Z },       [g~, u] its elements.
  ```
  `L_t` is a connected Lie group, `T = {[1, u]}` is a central circle, and `L_t / T = G`. Every connected Lie group
  with a central circle `T` and quotient `Sp_4(R)` is isomorphic to some `L_t` (remark in the proof; not used).

**Homogeneous model.** A homogeneous model of `E_3` is a triple `(t, Lambda, rho~)` with:
- `Lambda <= L_t` discrete, whose image `Lambda_0` in `G` is a lattice (cocompact or not);
- `rho~ : E_3 -> L_t` a homomorphism lifting the inclusion `Gamma <= G`;
- `rho~(z) not in Lambda`.

Then `E_3` acts on `P = L_t / Lambda` by left translation. `T` acts on `P` with finite stabilizer `Lambda cap T`,
and `P -> K = G / Lambda_0` is a principal `T/(Lambda cap T)`-bundle over the `Gamma`-space `K`. The element `z`
acts on the fibres as a nontrivial rotation of order 3.

When `Lambda_0` is cocompact, `Lambda cap T = 1` and the bundle is trivial, a `T`-equivariant trivialization
`P = K x T` turns the action into `g(y, u) = (g y, u + c(g, y))`, where `c` is a continuous untwisting in the sense
of (U) of `deligne-third-floor-failure-is-continuous-untwisting`, with `c(z, .) = 1/3` or `2/3`. This is the
natural Lie-theoretic candidate for refuting (NFA). The finite quotients `Lambda_0 / Lambda_0(N)` would then serve
as approximating finite `Gamma`-sets.

## Statement

Let `(t, Lambda, rho~)` be a homogeneous model, `m = |Lambda cap T|` and `t' = m t`.

- **(H1) The parameter is of order 3 or 6.** `t'` lies in `{1/3, 2/3, 1/6, 5/6}`. In particular `t' != 0` and
  `2 t' != 0`.
- **(H2) Splitting forces residual finiteness.** Let `n in {3, 6}` be the order of `t'`. Then there is a
  homomorphism `f : Lambda_0~ -> T` with `f(z) = -t'`. The map `(p, f)` embeds `Lambda_(0,n)` into
  `Lambda_0 x T`, so `Lambda_(0,n)` is residually finite.
- **(H3) Death.**
  - (a) *Unconditional.* If `Lambda_0` is commensurable with `g Sp_4(Z) g^(-1)` for some `g in G`, (H2)
    contradicts Deligne's residual `Res_fin(Gamma_n) = <z^2>`. So no homogeneous model exists over any such
    `Lambda_0`, for instance any congruence subgroup of `Sp_4(Z)`.
  - (b) *Under CSP.* By Margulis arithmeticity, `Lambda_(0,n)` is an arithmetic lattice in `G_n` with an
    associated absolutely almost simple, simply connected group `H` over a totally real field. If `H` has the
    congruence subgroup property, (H2) contradicts Deligne's theorem in the form of Stover's Theorem 3.3, since
    `n >= 3 > 2 >= #M(empty, H)`.

So, granted CSP for the `k`-forms of `Sp_4`, no lattice quotient of `Sp_4(R)` carries a homogeneous model of `E_3`.
This covers every compact one, and in particular every homogeneous continuous untwisting.

Caveat on scope. The commensurability class in (a) consists of non-uniform lattices, so (a) alone excludes no
compact `K`. For the compact quotients, which are the ones relevant to (U), the conclusion rests on (b) and hence
on CSP for anisotropic `k`-forms. Through `B_2 = C_2` these are spinor groups of 5-dimensional quadratic forms,
for which Kneser proved centrality of the congruence kernel. That identification and the precise hypotheses of
Kneser's theorem were not checked against a primary source here.

Only `Lambda cap T` finite is used, not discreteness of `Lambda`. (H1) uses only `rho~`, and (H2) uses only
`Lambda`.

## What this kills

**Named invariant.** `Res_fin(Lambda_(0,n))`, the finite residual of the `n`-fold cover of the lattice that
defines the space. Deligne's theorem, in either form, says it contains `<z^2>`, which is nontrivial for `n >= 3`.

**The class killed.** It kills refutations of the floor, and of (NFA), that build the untwisted space as a
homogeneous circle bundle `L_t / Lambda` over a locally symmetric space `Sp_4(R) / Lambda_0`, with the
approximating finite `Gamma`-sets taken from the quotients `Lambda_0 / Lambda_0(N)`. This is the Lie-theoretic
analogue of the discrete-phase systems killed by (C2) of `deligne-third-floor-failure-is-continuous-untwisting`,
and the most rigid kind of connected phase space that (C2) leaves open.

**Where it dies.** It dies at the lattice-splitting step, `Lambda <= L_t` with `Lambda cap T` finite over
`Lambda_0`. Such a `Lambda` gives a character `f` of `Lambda_0~` with `f(z) = -t'`. The character makes the `n`-fold
cover of `Lambda_0` linear, hence residually finite. (H1) forces `n >= 3`, and there Deligne's residual forbids
this.

**Calibration.** The method stops exactly at the metaplectic level. If `t'` were `1/2`, (H2) would give only
`Lambda_(0,2)` residually finite. This is true for congruence lattices, since `#M(empty, H) = |mu(k)| = 2` for
totally real `k`, and it matches the residual finiteness of the metaplectic double cover recorded in
`deligne-covers-of-sp2g-z-have-finite-residual-2z`. (H1) is what excludes `t' = 1/2` for `E_3`: the fibre
rotation `r` has order 3, and `D(Gamma)` is at most 2. So the obstruction sees precisely the part of the Deligne class that `mu(k)` cannot absorb.

## What it does not do

- It does not treat non-homogeneous systems, for example the universal affine system over a Cantor base found by
  another worker, or spaces with a `Gamma`-action that does not extend to `Sp_4(R)`.
- Only `L` with `L / T = Sp_4(R)` is treated. A larger Lie group `L`, with `Gamma` embedded differently, is not
  covered.
- `rho~` is assumed to lift the standard inclusion `Gamma <= Sp_4(R)`. Superrigidity makes this the natural case
  for a homomorphism into `L_t` with unbounded image, but no reduction is proved here.
- It gives non-existence, so it says nothing about finite approximability of other spaces. The floor stays OPEN.
- Part (b) assumes the congruence subgroup property for the relevant `k`-forms. Kneser's centrality theorem for
  `Spin(f)` with `dim f >= 5` would give it through `B_2 = C_2`, but that identification is not imported
  verbatim here.

## Attempts

- 2026-09-20 (swarm-0917-w21-w21-deligne-follow): **the CSP hypothesis of (b) is discharged.** Rapinchuk
  (Astérisque 209, 1992), Theorem 1, read from the scan, gives centrality of `C^S(G)` for simply connected
  `G` of types `B_n, C_n (n ≥ 2)` with `rang_S G ≥ 2`. It needs no isotropy hypothesis, and no identification
  with `Spin(f)` is needed.
  - This is imported in `sp4-forms-have-central-congruence-kernel`.
  - The unconditional statement over every lattice, cocompact included, is
    `deligne-homogeneous-bundle-models-die-over-every-lattice`.
  - This node's statement is unchanged.
