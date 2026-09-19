---
rg: 2
id: deligne-third-floor-above-fixed-level-proof
kind: route
title: Kill the torsion on a further cover, read virtual zero as inflation through Hochschild-Serre, and bound the denominators by the finite profinite multiplier
target: deligne-third-floor-holds-above-every-fixed-level
requires: [deligne-opnorm-monomial-models-are-almost-flat-circle-bundles, sp4-finite-index-fd-projective-multiplier-is-finite]
---

Notation of the target.

**Imported, verbatim.**
- From `sp4-finite-index-fd-projective-multiplier-is-finite` (ESTABLISHED), for every finite-index
  `Gamma' <= Sp_4(Z)`: "the natural map from the profinite completion `H^2_cts(Gamma'^, Q/Z) --> H^2(Gamma',T)` is
  injective with image exactly `R(Gamma')`, and its source is finite." Also: "`H_2(Sp_4(Z),Z)` has rank one".
- From its route `sp4-finite-index-multiplier-lazard-whitehead-proof`: "`Gamma(N)` has property (T)", and
  "Property (T) passes to finite-index subgroups and forces a finite abelianization".
- From `deligne-opnorm-monomial-models-are-almost-flat-circle-bundles` (ESTABLISHED):
  - (L2) "`||pi^* c||_cell = ||c||_cell` for every `c in H^2(Y_X; R)`";
  - (L3) "`kappa(Z_2(Y_X; Z)) = D(Lambda) Z` ... `D(Lambda)` lies in `{1, 2}`".

**Standard facts used** (no citation node).
- The Lyndon-Hochschild-Serre spectral sequence, with its edge maps.
- Naturality of the long exact coefficient sequences.
- Continuous cohomology of a profinite group with discrete coefficients is the colimit over its finite quotients
  (Serre, *Cohomologie galoisienne* I.2.2).

## Step 0: cellular versus group classes

`Y_X` is a finite 2-complex with `pi_1 = Lambda`. So `H_2(Y_X; Z) = Z_2(Y_X; Z)` is free of finite rank, and
Hopf gives `0 -> S_X -> H_2(Y_X) -> H_2(Lambda) -> 0`.

The classifying map `Y_X -> B Lambda` is an isomorphism on `H_1`. So `H^2(Lambda; A) -> H^2(Y_X; A)` is
injective, and its image is the classes vanishing on `S_X`. This holds for `A = Z, Q, R`, by the universal
coefficient theorem on both sides.

In particular:
- `H^2(Lambda; Z)` is finitely generated;
- `H^2(Lambda; Q) = Hom(H_2 Lambda, Q)`;
- the image `L^grp` of `H^2(Lambda; Z)` in `A_X = H^2(Lambda; R)` is a full lattice, since it spans the
  `Q`-structure `H^2(Lambda; Q)`.

An integral class on `Y_X` whose real class vanishes on `S_X` itself vanishes on `S_X`, because its values there
are integers. So it is a group class.

The covering `Y_(X') -> Y_(X_0)` is cellular and finite. Every class of `Y~` lies over both complexes, so
`pi_* S_(X') = S_(X_0)`. Hence `pi^*` maps `A_(X_0)` into `A_(X')`, and conversely: if `pi^* c` vanishes on
`S_(X')` then `c` vanishes on `S_(X_0)`. On `A` it is group restriction `res : H^2(Lambda_0) -> H^2(Lambda')`.
By (L2) it is injective on real classes, and it is defined over `Q`.

## Step 1: torsion dies virtually

Let `t in H^2(Lambda'; Z)` be torsion. Then `t` is killed on a finite-index subgroup.

- The sequence `H^1(Lambda'; Q/Z) --beta--> H^2(Lambda'; Z) -> H^2(Lambda'; Q)` is exact, and the second map
  kills exactly the torsion, by Step 0. So `t = beta(phi)` for a homomorphism `phi : Lambda' -> Q/Z`.
- `Lambda'` is finitely generated, so `phi` has finite image and `N := ker phi` has finite index.
- By naturality, `res_N t = beta(phi|N) = 0`.

## Step 2: virtually zero means inflated (degree 2)

*Lemma.* Let `Delta` be a finitely generated group, `A` a finite trivial module, and `x in H^2(Delta; A)`. Suppose
`res_N x = 0` for some finite-index `N <= Delta`. Then `x` is inflated from a finite quotient of `Delta`. Hence it
lies in the image of `H^2_cts(Delta^; A) -> H^2(Delta; A)`.

*Proof.*
1. Replace `N` by its normal core, which also has finite index. Write `Q = Delta / N`.
2. In the Hochschild-Serre filtration of `(Delta, N)`, the edge map `H^2(Delta) -> E_infty^(0,2) <= H^2(N)^Q` is
   restriction. So `x in F^1`.
3. `N` is finitely generated and `A` is finite, so `Hom(N, A)` is finite. Put
   `N' := intersection of ker(h)` over all `h in Hom(N, A)`. It is characteristic in `N`, hence normal in
   `Delta`, and it has finite index. Every `h` vanishes on `N'`.
4. The identity of `Delta`, the inclusion `N' <= N` and the surjection `Q' := Delta / N' -> Q` give a morphism of
   spectral sequences `E_r(Delta, N) -> E_r(Delta, N')`. It is the identity on the abutment `H^*(Delta; A)`, and it
   respects the filtrations.
   - So `x in F^1(N')`.
   - The class of `x` in `E_infty^(1,1)(N')` is the image of its class in `E_infty^(1,1)(N)`.
   - On `E_2^(1,1)`, the map `H^1(Q; Hom(N, A)) -> H^1(Q'; Hom(N', A))` is induced by restriction
     `Hom(N, A) -> Hom(N', A)`, which is zero by the choice of `N'`.
   - So the `E_infty^(1,1)(N')` class of `x` is zero, and `x in F^2(N')`.
5. `F^2(N') = E_infty^(2,0)` is the image of inflation `H^2(Q'; A) -> H^2(Delta; A)`. This inflation factors
   through `Delta^`. QED.

## Step 3: the lattice `M(Lambda_0)`

Write `q : H^2(Lambda_0; Q) -> H^2(Lambda_0; Q/Z)` for the coefficient map.
- Its kernel is the image of `H^2(Lambda_0; Z)`, which is `L^grp_0`.
- Let `I_0` be the image of the natural map `G_0 = H^2_cts(Lambda_0^; Q/Z) -> H^2(Lambda_0; Q/Z)`. It is finite
  (import).
- Put `M(Lambda_0) := q^(-1)(I_0)`, a subgroup of `H^2(Lambda_0; Q) <= A_(X_0)`.
- `q` induces an injection `M / L^grp_0 -> I_0`. So `[M : L^grp_0] <= |G_0|`, and `M` is a full lattice.
- `L_(X_0) cap A_(X_0) = L^grp_0` by Step 0.

*(F1).* Let `c in A_(X_0)` with `pi^* c in L_(X')`.
1. `pi^*` is injective and defined over `Q`, and `pi^* c` is rational. So `c in H^2(Lambda_0; Q)`. Choose `m >= 1`
   and `u in H^2(Lambda_0; Z)` with `u_R = m c`.
2. Pick `w~ in H^2(Y_(X'); Z)` with `w~_R = pi^* c`. Then `pi^* c in A_(X')`, so `w~` is a group class `w` (Step 0).
3. `res u - m w` has zero real class, so it is a torsion class `t`.
4. By Step 1 there is a finite-index `N <= Lambda'` with `res_N t = 0`. So `res_N u = m res_N w`, and
   `res_N (u mod m) = 0`.
5. By Step 2, applied to `Delta = Lambda_0` (finitely generated) and `A = Z/m`, `u mod m` is in the image of
   `H^2_cts(Lambda_0^; Z/m)`.
6. Let `j : Z/m -> Q/Z` send `1` to `1/m`. The composite `Z -> Z/m -> Q/Z` equals `Z -> Q -> Q/Z` with
   `1 -> 1/m`. Hence

   ```text
   q(c) = q(u (x) 1/m) = j(u mod m).
   ```

7. Inflation is natural in the coefficients, so `j(u mod m) in I_0`. Hence `c in M(Lambda_0)`.

## Step 4: (F2) and (F3)

*(F2).* `nu(Lambda_0) > 0`, since `M` is a lattice in the finite-dimensional normed space `(A_(X_0), ||.||_cell)`.

Now take `f` as in (F2).
- `f_R = pi^* c` for some `c in A_(X_0)`, by Step 0.
- `f_R in L_(X')`, so `c in M` by (F1).
- By (L3) there is `Sigma' in Z_2(Y_(X'); Z)` with `kappa'(Sigma') = D in {1, 2}`. So
  `f(Sigma') = D + 3 g(Sigma') != 0`, and therefore `c != 0`.
- By (L2), `||f_R|| = ||c|| >= nu(Lambda_0)`.

*The case `Lambda_0 = Gamma`.* `H_2(Sp_4(Z), Z)` has rank one (import), so `A_Y` is a line. It contains
`kappa_R`, since `kappa` vanishes on `S` by (K1). So pulled-back classes are exactly the Kahler-proportional ones.

*(F3).* Suppose `res u = m w + t` with `t` torsion. Then `pi^*(u_R / m) = w_R in L_(X')`. By (F1),
`u_R / m in M`. `M` is a lattice and `u_R != 0`, so `m` divides the finite divisibility index of `u_R` in `M`.

## Step 5: (T), the torsion class at level 3

1. Let `Lambda = Gamma(3)`. The map `1 + 3Z -> Z mod 3` is a homomorphism `Gamma(3) -> M_4(F_3)`, because
   `(1 + 3Z)(1 + 3Z') = 1 + 3(Z + Z') + 9 Z Z'`. It is nonzero on the transvection `1 + 3E`, where `E` is an
   elementary symplectic nilpotent. So `Hom(Gamma(3), Z/3) != 0`.
2. `H_1(Gamma(3))` is finite by property (T) (import). Hence `H_1 / 3 H_1 != 0`.
3. `Ext(H_1, Z)` is the Pontryagin dual of `H_1`. So it also has `Ext / 3 Ext != 0`. Pick `t in Ext`, not in
   `3 Ext`.
4. In `H^2(Y_X; Z)`, the torsion subgroup is exactly `Ext(H_1, Z)`, because `Hom(H_2, Z)` is free. If `t = 3y`,
   then `y` is torsion, so `y in Ext`, a contradiction. So `t notin 3 H^2(Y_X; Z)`.
5. `t` is torsion, so it vanishes on the free group `Z_2`. In particular `t|S_X = 0` and `t_R = 0`, which gives
   `||t_R||_cell = 0`.

The repaired condition assumes `u(Z_2)` is not contained in `3Z`. That excludes `t`. The implication "repaired
condition plus (K1) implies the floor" is the same argument as in the floor node, since the residual `f` has
`f(Sigma) = D mod 3`. The repaired condition itself stays open.
