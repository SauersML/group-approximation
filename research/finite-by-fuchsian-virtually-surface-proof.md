---
rg: 2
id: finite-by-fuchsian-virtually-surface-proof
kind: route
title: Selberg's lemma, then kill the Euler class of a central extension by a cover of degree |Z(K)|
target: finite-by-cocompact-fuchsian-groups-are-virtually-surface
requires: []
---

Write `pi: P -> Phi` for the quotient map, with finite kernel `K`.

## Step 1: a torsion-free orientation-preserving subgroup of Phi

- `Isom(H^2)` is isomorphic to `O^+(2,1)`, the subgroup of `O(2,1)` preserving the upper sheet of
  the hyperboloid. So it is a subgroup of `GL_3(R)`.
- `Phi` is discrete, and point stabilizers in `Isom(H^2)` are compact. So `Phi` acts properly
  discontinuously on `H^2`, and cocompactly by hypothesis. By Svarc--Milnor, `Phi` is finitely
  generated.
- By Selberg's lemma (a finitely generated subgroup of `GL_n` of a field of characteristic `0`
  is virtually torsion-free), there is a torsion-free subgroup `Phi'` of finite index in `Phi`.
- Put `Phi_0 = Phi' ∩ Isom^+(H^2)`, of index at most `2` in `Phi'`.
- A nontrivial element of `Phi_0` fixing a point of `H^2` lies in a compact point stabilizer
  intersected with a discrete group, so it has finite order. That is impossible, so `Phi_0` acts
  freely.
- Therefore `H^2 -> S := H^2/Phi_0` is a covering map, and `Phi_0 ≅ pi_1(S)`.
  - `S` is orientable, because `Phi_0` preserves orientation.
  - `S` is compact, because `Phi_0` has finite index in the cocompact group `Phi`.
  - `S` has a hyperbolic metric, so Gauss--Bonnet gives `area(S) = -2 pi chi(S) > 0`, hence
    genus at least `2`.
- `S` is a `K(Phi_0, 1)`, since `H^2` is contractible.

## Step 2: a central extension of a surface group

- Put `P_0 = pi^{-1}(Phi_0)`, so `[P : P_0] = [Phi : Phi_0]` is finite.
- `K` is normal in `P_0`. Conjugation gives a homomorphism `P_0 -> Aut(K)` to a finite group.
  Let `C` be its kernel, which has finite index in `P_0`.
- `C ∩ K` is the centralizer of `K` in `K`, namely `A := Z(K)`, a finite abelian group.
- `Phi_1 := pi(C)` has finite index in `Phi_0`, and `ker(pi|_C) = C ∩ K = A`. So
  `1 -> A -> C -> Phi_1 -> 1` is exact.
- It is a central extension, because `C` centralizes `K`, which contains `A`.
- `Phi_1` is a finite-index subgroup of `Phi_0`. So `S_1 := H^2/Phi_1` is a closed orientable
  hyperbolic surface covering `S`, and a `K(Phi_1, 1)`.

If `A = 1`, then `C ≅ Phi_1` already works, with `Sigma = C`. Otherwise:

## Step 3: the extension class dies in a cover of degree |A|

Let `e ∈ H^2(Phi_1; A)` be the class of the central extension, with trivial coefficients. The
following facts are standard (see K. S. Brown, *Cohomology of Groups*, Chapter IV, for F1 and F2;
no theorem numbers are checked here).

- **F1.** An extension of `Q` by an abelian group `A` with a given action splits, meaning it has
  a homomorphic section, if and only if its class in `H^2(Q; A)` is `0`.
- **F2.** For a subgroup `Q' <= Q`, the extension `1 -> A -> pi^{-1}(Q') -> Q' -> 1` has class
  `res(e)`. Proof: if `s: Q -> E` is a set-theoretic section with `s(1) = 1`, the class is
  represented by `f(x,y) = s(x)s(y)s(xy)^{-1}`, and restricting `s` to `Q'` restricts `f`.
- **F3.** For an aspherical space `X` with `pi_1 X = Q`, `H^2(Q; A) = H^2(X; A)`. The
  identification is natural, and for a covering `p: X' -> X` corresponding to `Q' <= Q`,
  restriction corresponds to `p^*`.
- **F4.** Universal coefficients: `H^2(X; A)` is an extension of `Hom(H_2(X;Z), A)` by
  `Ext(H_1(X;Z), A)`, and the map to `Hom` is evaluation, natural in `X`.
  - For a closed orientable surface, `H_1` is free abelian, so the `Ext` term is `0`.
  - Also `H_2 = Z[S]`.
  - So `ev_[S]: H^2(S; A) -> A` is an isomorphism.
- **F5.** A connected `d`-sheeted covering `p: S_2 -> S_1` of closed surfaces, with `S_2` given
  the lifted orientation, satisfies `p_*[S_2] = d [S_1]`.

Now let `d = |A|`.

- `H_1(S_1; Z) ≅ Z^{2g_1}` with `g_1 >= 2`. So there is a surjection `Phi_1 -> Z -> Z/d`. Its
  kernel `Phi_2` has index `d`, and `S_2 := H^2/Phi_2 -> S_1` is a connected `d`-sheeted
  covering.
- By F3, F4 and F5, `<res(e), [S_2]> = <p^* e, [S_2]> = <e, p_*[S_2]> = d <e, [S_1]> = 0`, since
  `d` kills every element of `A` by Lagrange.
- By F4 for `S_2`, `res(e) = 0`.
- Let `C_2 = C ∩ pi^{-1}(Phi_2)`, which has index `d` in `C`. By F2 it carries the extension
  `1 -> A -> C_2 -> Phi_2 -> 1` with class `res(e) = 0`.
- By F1 there is a homomorphism `s: Phi_2 -> C_2` with `pi ∘ s = id`, so `s` is injective.
- Put `Sigma := s(Phi_2) ≅ Phi_2 ≅ pi_1(S_2)`. Here `S_2` is closed and orientable, with
  `chi(S_2) = d chi(S_1) < 0`, so its genus is at least `2`.

## Step 4: finite index

- `pi` is injective on `Sigma` and kills `A`, so `A ∩ Sigma = 1`.
- For `c ∈ C_2`, `c · s(pi(c))^{-1}` lies in `A`, so `C_2 = A · Sigma` and `[C_2 : Sigma] = |A|`.
- Hence `[P : Sigma] = [P : P_0][P_0 : C][C : C_2][C_2 : Sigma]` is finite.

## Step 5: quasiconvexity

In a hyperbolic group `G`, a subgroup is quasiconvex if and only if it is finitely generated and
undistorted, meaning the inclusion is a quasi-isometric embedding for word metrics. This is
standard.

- If `P` is quasiconvex in `G`, it is finitely generated and undistorted.
- `Sigma` has finite index in `P`, so it is finitely generated and the inclusion `Sigma -> P` is a
  quasi-isometry.
- The composite `Sigma -> G` is a quasi-isometric embedding, so `Sigma` is quasiconvex in `G`.
