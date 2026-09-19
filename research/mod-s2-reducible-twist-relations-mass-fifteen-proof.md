---
rg: 2
id: mod-s2-reducible-twist-relations-mass-fifteen-proof
kind: route
title: Reducible monodromy lands in a conjugate of SL2xSL2 (up to an index-two swap) or of a maximal parabolic, where Deligne's class is a circle coboundary, and the commutator-lift count of the Maslov line then sees z only to exponents divisible by 3
target: mod-s2-reducible-twist-relations-have-mass-divisible-by-fifteen
requires:
  - deligne-multiplier-trivial-on-sl2xsl2-and-parabolics
  - mod-s2-torelli-characters-have-a-metaplectic-maslov-line
  - genus-two-torelli-freely-generated-by-separating-twists
  - mod-s2-real-untwisting-identifies-deligne-norm-parameters
---

Notation as in the target. Inputs:
- **[P]** `deligne-multiplier-trivial-on-sl2xsl2-and-parabolics`. Let `S = SL_2(Z) x SL_2(Z)` be block diagonal on
  `<e_1,f_1> + <e_2,f_2>`, let `P_S` be the stabilizer of `Z e_1 + Z e_2`, and let `P_K` be the stabilizer of `Z e_1`.
  For each of these three subgroups `Q`, there is a homomorphism `p^-1(Q) -> T` (preimage in `E_3`) with
  `z -> omega`. Equivalently, `alpha|_Q = 0` in `H^2(Q; T)`.
- **[ML]** `mod-s2-torelli-characters-have-a-metaplectic-maslov-line`: `r = f(t_s) = +-1/5` (ML0).
- **[U1]** `mod-s2-real-untwisting-identifies-deligne-norm-parameters`: `f : M -> R` with
  `f(x) + f(x') - f(xx') = b(pi x, pi x')`, where `b` is the integral cocycle of `Gamma~ = Gamma x_b Z`, and
  `f|_K = r F`.
- **[Mess]** `genus-two-torelli-freely-generated-by-separating-twists`: `F : K -> Z` is a homomorphism with
  `F(t_s) = 1`.
- **Classical facts, used by citation.**
  - (W) Witt's theorem over `Z`: every primitive isotropic sublattice of the unimodular symplectic lattice `Z^4`
    extends to a symplectic basis. So it is `Sp_4(Z)`-conjugate to `Z e_1` or to `Z e_1 + Z e_2`, and every
    unimodular symplectic splitting `P + P^perp` is conjugate to `<e_1,f_1> + <e_2,f_2>`.
  - (G) In `S_2`, two disjoint essential separating curves are isotopic. Two disjoint curves have algebraic
    intersection `0`.
  - (C3) `Gamma(3)` is torsion-free (Minkowski/Serre). A torsion-free virtually free group is free (Stallings).
  - (Sw) Swan's extension of Stallings' theorem: a torsion-free virtually free group is free, with no finite
    generation hypothesis. `H^2(free; T) = 0`.

Write `B^` for the preimage of `B <= Gamma` in `E_3 = Gamma~/<z^3>`, and `B~` for its preimage in `Gamma~`. Let
`q : Gamma~ -> E_3` be the quotient map, so `q(B~) = B^` and `q(z)` generates the kernel `C_3` of `E_3 -> Gamma`.
Write `omega` also for the image of `q(z)` under the inclusion `C_3 -> T`, `q(z)^j -> omega^j`.

## Step 0: circle-flexibility and its permanence

Call `B <= Gamma` **T-flexible** if `alpha|_B = 0` in `H^2(B; T)`.

- **(a) Character form.** `B` is T-flexible iff there is a homomorphism `phi : B^ -> T` with `phi(q z) = omega`.
  - Let `E_T = (B^ x T)/{(q(z)^j, omega^-j)}` be the pushout of `B^` along `C_3 -> T`. It is the central
    `T`-extension of `B` with class `alpha|_B` (image under the coefficient map).
  - If the class is zero, `E_T = T x B` as groups over `B`, compatibly with the inclusion of `T`. The composite
    `B^ -> E_T -> T` of the canonical map and the projection is a homomorphism sending `q(z)` to `omega`.
  - Conversely, given `phi`, the map `b -> [(b^, phi(b^)^-1)]` is independent of the lift `b^` and is a
    homomorphic section of `E_T -> B`. So the class vanishes.
- **(b) Subgroups and conjugates.** Restricting `phi` shows that subgroups of T-flexible groups are T-flexible.
  For `g in Gamma`, pick `g^ in E_3` over `g`. Then `phi o c_(g^)^-1` is a character of `(g B g^-1)^` with
  `q(z) -> omega`, since `q(z)` is central. So conjugates of T-flexible groups are T-flexible.
- **(c) Overgroups of index prime to 3.** Let `B <= B'` with `[B':B] = e` finite and `3 not| e`, and let `B` be
  T-flexible. The class `alpha|_(B')` is the image of a `Z/3` class, so `3 alpha|_(B') = 0`. Also
  `cor o res = e` on `H^2(B'; T)`, so `e alpha|_(B') = cor(alpha|_B) = 0`. Since `gcd(e, 3) = 1`,
  `alpha|_(B') = 0`.
- **(d) The z-exponent test.** If `B` is T-flexible and `z^n in [B~, B~]`, then `3 | n`. Indeed `phi o q` is a
  homomorphism `B~ -> T`, so it kills `[B~, B~]`. Hence `1 = phi(q(z))^n = omega^n`.

## Step 1: reducible images are T-flexible (RT1)

Let `A` preserve the essential multicurve `C`, and let `x in A`. Then `x` permutes the isotopy classes of the
components of `C`, and it preserves the separating/nonseparating type of each.

- *Case (i): `C` has a nonseparating component.* Let `L <= H_1(S_2; Z) = Z^4` be spanned by the classes of the
  nonseparating components, each up to sign.
  - `L` is nonzero, since a nonseparating curve has a primitive nonzero class. It is isotropic by (G).
  - `pi(x)` permutes the set of classes `+-[c]`, so it preserves `L` and its saturation
    `L^s = (L tensor Q) cap Z^4`. That is a primitive isotropic sublattice of rank 1 or 2.
  - By (W), `g L^s = Z e_1` or `g L^s = Z e_1 + Z e_2` for some `g in Gamma`. Then `g pi(A) g^-1 <= P_K` or
    `<= P_S`.
  - By [P] and (b), `pi(A)` is T-flexible.
- *Case (ii): every component is separating.* By (G), `C = {s}` for one separating curve `s`.
  - `s` cuts `S_2` into two one-holed tori with homology `P` and `P^perp`. These are unimodular symplectic
    planes, and `P + P^perp = Z^4`.
  - `x` maps `s` to itself up to isotopy, so it permutes the two sides. Hence `pi(A)` lies in the stabilizer
    `S_P^+-` of the unordered pair `{P, P^perp}`.
  - `S_P^+-` contains `S_P = Sp(P) x Sp(P^perp)` with index at most `2`.
  - By (W), `S_P` is conjugate to `S`. By [P] and (b), `S_P` is T-flexible. By (c) with `e <= 2`, so is
    `S_P^+-`. By (b), so is `pi(A)`.

## Step 2: localized commutator lifts (RT2)

Take `b` normalized, `b(1, g) = b(g, 1) = 0`, as in [U1]. (A cocycle satisfies `b(1,g) = b(g,1) = b(1,1)`,
and subtracting the constant coboundary normalizes it; [U1] then gives `f(1) = 0`.) Write
`Gamma~ = Gamma x_b Z` with `(g,n)(g',n') = (g g', n + n' + b(g,g'))` and `z = (1,1)`, so `(1,n) = z^n`.

- Let `P = M x_Gamma Gamma~ = {(x, n) : x in M, n in Z}`, with the product induced from `Gamma~`.
  Put `mu(x, j) = j + f(x)`. By [U1],
  `mu((x,j)(x',j')) = j + j' + b(pi x, pi x') + f(x x') = mu(x,j) + mu(x',j')`. So `mu : P -> R` is a
  homomorphism, and it kills `[P, P]`.
- Let `k = prod_i [x_i, y_i]` with `x_i, y_i in A` (in particular in `A cap H`) and `k in K`. Put
  `X_i = (x_i, 0)`, `Y_i = (y_i, 0)`. Then `prod_i [X_i, Y_i] = (k, n)` for some `n in Z`.
- `mu(k, n) = 0`, so `n = -f(k) = -r F(k)` by [U1].
- The projection `P -> Gamma~` is a homomorphism. It sends `(k, n)` to `(1, n) = z^n`, and it sends
  `prod_i [X_i, Y_i]` into `[B~, B~]`, since `pi(x_i), pi(y_i) in pi(A) <= B`. So `z^n in [B~, B~]`.
- By Step 0 (d), `3 | n`. With `r = +-1/5` from [ML], `F(k) = -+ 5 n in 15 Z`.

This proves (RT2), and in fact `F(K cap [A, A]) <= 15 Z` without reference to `H`.

## Step 3: sums of local relations (RT3)

- Let `G_loc` be the subgroup of `K` generated by the groups `K cap [A cap H, A cap H]`, `A` reducible. By
  Step 1 each `pi(A)` is T-flexible, so by Step 2 `F` maps each generating group into `15 Z`. Since `F` is a
  homomorphism on `K` [Mess], `F(G_loc) <= 15 Z`.
- `nu` is a homomorphism and `F = sum_o nu_o`, so `L_loc(H) = nu(G_loc)` has coordinate sums in `15 Z`.
  - `F(L(H)) = 5 m Z` with `m in {1, 2}` [ML], and `5m not in 15 Z`. So `L_loc(H) != L(H)`.
  - For `l in L_loc(H)`, `<(1/3) 1, l> = F(l)/3 in 5 Z`, which is `0` in `R/Z`.
  - `F(t_(s_1)^(n_1) ... t_(s_k)^(n_k)) = sum n_j` by [Mess]. If such a product lies in `G_loc`, then
    `sum n_j in 15 Z`, so `3 | sum n_j`.

## Step 4: congruence-deep images (RT4)

Let `Gamma' <= Gamma(3)` and let `pi(A)` be finite or virtually free. Then
`pi(A cap H) <= B := pi(A) cap Gamma(3)`. By (C3), `B` is torsion-free. It is a subgroup of a finite or
virtually free group, so it is trivial or free by (Sw). Hence `H^2(B; T) = 0`, and `B` is T-flexible. Step 2,
applied to `A cap H` and `B`, gives `F(K cap [A cap H, A cap H]) <= 15 Z`.

## Remark: why this does not contradict (ML1)

No finite-index `B <= Gamma` is T-flexible. A character `phi : B^ -> T` with `phi(q z) = omega` has image a
finitely generated abelian group; composing with a map to a finite cyclic quotient that is injective on
`<omega>` gives a finite quotient of `B^` in which `q(z)` survives. Deligne's theorem says that every
finite-index subgroup of `E_3` kills `q(z)` in every finite quotient. So the `5m` relations of (ML1) must use
monodromy that is not T-flexible, which is the dichotomy recorded in the target.
