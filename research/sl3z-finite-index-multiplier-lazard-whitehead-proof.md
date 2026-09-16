---
rg: 2
id: sl3z-finite-index-multiplier-lazard-whitehead-proof
kind: route
title: Finite-dimensional classes are profinite, the congruence completion splits, and sl_3 has no second cohomology
target: sl3z-finite-index-fd-projective-multiplier-is-finite
requires:
  - sl3z-finite-index-subgroups-are-congruence-subgroups
  - sl3z-schur-multiplier-is-klein-four
  - ershov-jaikin-kassabov-steinberg-groups-have-property-t
artifacts:
  - experiments/sl3z-finite-index-multiplier-2026-09-16/sl3-chevalley-eilenberg-betti.py
---

This is the argument of `sp4-finite-index-multiplier-lazard-whitehead-proof` run at `SL_3`.
Step 0 and the pro-`l` part of Step 4 do not depend on the group. The changes are:
- the level-one input, now `sl3z-schur-multiplier-is-klein-four`;
- the Lie algebra, now `sl_3` of dimension 8;
- Step 1, where density of `SL_3(Z)` in `SL_3(Z^)` is elementary.

**Sources.**
- **Lazard.** *Groupes analytiques p-adiques*, Publ. IHES 26 (1965), chapter V. The source check
  of (2.2.2.2)--(2.2.3.2) (quasi-minimal complexes, pp. 165--166) and (2.4.9)--(2.4.10)
  (comparison with Lie algebra cohomology, pp. 178--179) is recorded in
  `sp4-finite-index-multiplier-lazard-whitehead-proof`, which read the PDF on 2026-09-12. It was
  not re-read this session. Both statements are for arbitrary complete `p`-valued groups of
  finite rank, so they apply unchanged.
- **Whitehead.** `H^2(g, k) = 0` for a semisimple Lie algebra `g` over a field `k` of
  characteristic 0. It is model-tested for `g = sl_3` by the artifact, an exact rank computation
  over `Q` giving `(b_1, b_2, b_3) = (0, 0, 1)`, with calibrations abelian `Q^2` `(2, 1, 0)`,
  `heis_3` `(2, 2, 1)`, `sl_2` `(0, 0, 1)` and `gl_3` `(1, 0, 1)`. Over `Q_p` the
  Chevalley--Eilenberg complex is the base change of the one over `Q`, so `b_2 = 0` there too.
- **Classical, not re-read.**
  - Malcev: finitely generated linear groups are residually finite.
  - Continuous cohomology of a profinite group with discrete coefficients is the colimit over
    finite quotients, and there is a Hochschild--Serre spectral sequence (Serre, *Cohomologie
    galoisienne*, I.2.2 and I.2.6).
  - Property (T) passes to finite-index subgroups and forces finite abelianization (BdlHV
    1.7.1 and 1.3.6).

**Notation.**
- `Γ = SL_3(Z)` and `Γ(m) = ker(Γ -> SL_3(Z/m))`.
- Profinite groups carry continuous cohomology with discrete coefficients.
- Undecorated `H^n(-)` means `H^n(-, Q/Z)`.
- `Γ` has (T) by `ershov-jaikin-kassabov-steinberg-groups-have-property-t` (type `A_2`, `R = Z`;
  `E_(A_2)(Z) = EL_3(Z) = SL_3(Z)`). Hence every finite-index subgroup has finite
  abelianization.

## Step 0: finite dimension means profinite

*Lemma.* Let `Δ` be a finitely generated residually finite group. Then `R(Δ)` is the image of
`H^2(Δ^) -> H^2(Δ, T)`. If `Δ^ab` is finite, the map is injective.

*The image lies in `R`.*
- Take a finite quotient `q: Δ -> Q` and `b ∈ Z^2(Q, μ_m)`.
- On `l^2(Q)` put `λ_b(x)δ_y = b(x, y)δ_(xy)`. The cocycle identity gives
  `λ_b(x)λ_b(x') = b(x, x')λ_b(xx')`.
- So `λ_b ∘ q` realizes `inf[b]`.

*`R` lies in the image.*
- Let `π: Δ -> U(d)` have cocycle `c`. Rescale each `π(g)` by a `d`-th root of
  `det π(g)^(-1)` to get `u(g) ∈ SU(d)`. Then `u(g)u(h) = c'(g, h)u(gh)`, where `c'` takes values
  in `μ_d` (take determinants) and `[c'] = [c]` in `H^2(Δ, T)`.
- `E = {(g, x) ∈ Δ × SU(d) : x ∈ μ_d u(g)}` is a central extension
  `1 -> μ_d -> E -> Δ -> 1` with class `[c']`.
- `E` is finitely generated and lies in `Δ × pr_2(E)`. Both factors are residually finite, the
  second by Malcev. So `E` is residually finite, and some finite-index normal `N ⊲ E` has
  `N ∩ μ_d = 1`.
- Put `Q = E/(N μ_d)`, a finite quotient of `Δ`. The map `E -> Δ ×_Q (E/N)` is an isomorphism.
  - Injectivity is `N ∩ μ_d = 1`.
  - For surjectivity, lift the `Δ`-coordinate and correct by an element of `μ_d`.
- So `[c']` is inflated from the finite central extension `E/N` of `Q`.

*Injective when `Δ^ab` is finite.*
- Let `b ∈ Z^2(Q, μ_k)` with `inf b = δf` for some `f: Δ -> T`.
- Then `f^k` is a homomorphism `Δ -> T`. It factors through the finite group `Δ^ab`, so it has
  finite order `e`, and `f` takes values in `μ_(ke)`.
- `g ↦ (q(g), f(g)^(-1))` is a homomorphism into the finite twisted product `Q ×_b μ_(ke)`.
  Its kernel `L` has finite index, and `f` is constant on `L`-cosets.
- Over `Δ/L`, `inf b` is the coboundary of the induced `μ_(ke)`-valued function. So `[b]` dies
  in the colimit.

## Step 1: congruence completion

- By `sl3z-finite-index-subgroups-are-congruence-subgroups`, every finite-index subgroup of
  `Γ` contains some `Γ(m)`, and every reduction `Γ -> SL_3(Z/m)` is onto.
- Hence `Γ` is dense in `SL_3(Z^) = prod_p SL_3(Z_p)`, and `Γ^ = SL_3(Z^)`.
- For every open `W <= Γ^`, the closure of `Γ ∩ W` is `W`, since a dense set meets an open set
  densely.
- Let `K <= Γ` have finite index, with `Γ(m) <= K`, and put `N = m^2`. Then `Γ(N) <= K` and
  `v_p(N) >= 2` for every `p | N`.
- Every finite-index subgroup of `K` has finite index in `Γ`. So the profinite topology of `K`
  is the congruence topology, and `U := K^` is the closure of `K`, an open subgroup of `Γ^`.
- The closure of `Γ(N)` is `V = ker(SL_3(Z^) -> SL_3(Z/N)) = K_S × G^S`, where:
  - `K_S = prod_(p | N) K_p` and `K_p = ker(SL_3(Z_p) -> SL_3(Z/p^(v_p(N))))`;
  - `G^S = prod_(p ∤ N) SL_3(Z_p)`.
- `V` is open and normal in `U`, and `U/V` is finite.

## Step 2: Hochschild--Serre bookkeeping

For a profinite group `A` and a closed normal subgroup `B`, the Hochschild--Serre spectral
sequence with trivial discrete coefficients `Q/Z` filters `H^2(A)`. Its graded pieces are
subquotients of `E_2^(2,0)`, `E_2^(1,1)` and `E_2^(0,2)`, so

```text
|H^2(A)|  <=  |H^2(A/B)| . |H^1(A/B, H^1(B))| . |H^2(B)| .                   (HS)
```

*Every `H^1` term below is finite.*
- `H^1(V) = Hom_cts(V, Q/Z)`. Restriction to the dense subgroup `Γ(N)` is injective, and
  `Hom(Γ(N), Q/Z)` is finite because `Γ(N)` has (T), so `Γ(N)^ab` is finite.
- A direct factor `P` of `V` has `H^1(P)` embedded in `H^1(V)` through the projection.
- For finite abelian `M`, `Hom_cts(P, M)` is finite: `M` embeds in some `(Q/Z)^r`, so
  `Hom_cts(P, M)` embeds in `H^1(P)^r`.

*Apply (HS).*
- **`A = U`, `B = V`.** `U/V` is finite, so `H^2(U/V)` is finite. `H^1(V)` is finite, so the
  cochains of `U/V` in it are finitely many. It remains to bound `H^2(V)`.
- **`A = V = K_S × G^S`, `B = G^S`.** `K_S` acts trivially on `H^*(G^S)` (it commutes with
  `G^S`). So `E_2^(1,1) = Hom_cts(K_S, H^1(G^S))`, which is finite. It remains to bound
  `H^2(K_S)` and `H^2(G^S)`.
- **`K_S`.** It is a finite product of direct factors `K_p` of `V`. The same step, applied one
  prime at a time, reduces it to the `H^2(K_p)`.

## Step 3: almost all primes, from level one

- `SL_3(Z^) = (prod_(p | N) SL_3(Z_p)) × G^S`, and the projection onto `G^S` has the obvious
  section. So inflation `H^2(G^S) -> H^2(SL_3(Z^))` is injective, with left inverse the pullback
  along the section.
- `SL_3(Z^) = Γ^` (Step 1), and `Γ` is perfect, so Step 0 embeds `H^2(Γ^)` in `H^2(Γ; T)`.
- `H^2(Γ; T) ≅ Hom(H_2(Γ; Z), T) ≅ Hom(Z/2 × Z/2, T)` has order 4 by
  `sl3z-schur-multiplier-is-klein-four`. The universal coefficient theorem is used here;
  `Ext(H_1, T) = 0` since `T` is divisible.
- Hence `|H^2(G^S)| <= 4`.

## Step 4: the finitely many primes, Whitehead through Lazard

Fix `p | N`, and put `L := K_p` and `v := v_p(N) >= 2`. Then
`H^2(L) = (+)_l H^2(L, Q_l/Z_l)`.

*`l != p`.*
- `L` is pro-`p`: for `w >= v` its quotient by `ker(SL_3(Z_p) -> SL_3(Z/p^w))` has order
  `p^(8(w - v))`.
- `H^n(L, Q_l/Z_l)` is the colimit of `H^n(P, Q_l/Z_l)` over finite `p`-group quotients `P`.
- For `n >= 1` each of these is killed by `|P|`, which acts invertibly on an `l`-primary module.
  So all of them vanish.

*`l = p`.*
- **`L` is `p`-valued.** Put `ω(g) := v_p(g - 1)`, the minimum valuation of the matrix entries.
  Then `ω(g) >= v >= 2 > 1/(p - 1)` on `L`. Write `X = g - 1` and `Y = h - 1`.
  - `gh - 1 = X + Y + XY` and `h^(-1) - 1 = -h^(-1)Y`, so
    `ω(gh^(-1)) >= min(ω(g), ω(h))`.
  - `[g, h] - 1 = g^(-1)h^(-1)(XY - YX)`, so `ω([g, h]) >= ω(g) + ω(h)`.
  - Let `ω(g) = j >= 2` and expand `g^p - 1 = pX + sum_(1<i<p) C(p, i)X^i + X^p`.
    - `pX` has valuation exactly `j + 1`.
    - The middle terms have valuation `>= 1 + 2j`.
    - `X^p` has valuation `>= pj >= 2j >= j + 2`.
    - So `ω(g^p) = ω(g) + 1`.
  - `L` is open in `SL_3(Z_p)`, so it is a complete `p`-valued group of rank `dim sl_3 = 8`.
- **Coefficient sequence.** `0 -> Z_p -> Q_p -> Q_p/Z_p -> 0` gives a short exact sequence of
  continuous cochain complexes. It is onto at the cochain level: a continuous map from compact
  `L^n` to discrete `Q_p/Z_p` is constant on the pieces of a finite open partition, so it lifts.
  Hence

  ```text
  H^2_c(L, Q_p)  -->  H^2(L, Q_p/Z_p)  -->  H^3_c(L, Z_p)      is exact.
  ```

- **Whitehead.** The `Q_p`-Lie algebra of `L` is `sl_3(Q_p)`. By Lazard V (2.4.9),
  `H^2_c(L, Q_p)` is computed by the Lie algebra cohomology `H^2(sl_3(Q_p), Q_p)`, which is `0`
  by Whitehead and the artifact. The conclusion is still `0` if one uses only the
  `L`-invariant part of the Lie algebra cohomology. So `H^2(L, Q_p/Z_p)` embeds in
  `H^3_c(L, Z_p)`.
- **Finiteness.** By Lazard V (2.2.2.2)--(2.2.3.2), `H^3_c(L, Z_p)` is the cohomology of a
  quasi-minimal complex with `Hom_A(X_n, Z_p) = Z_p^(C(8, n))`. So it is a finitely generated
  `Z_p`-module.
- `H^2(L, Q_p/Z_p)` is torsion, so it embeds in the torsion submodule of `H^3_c(L, Z_p)`, which
  is finite.

## Step 5: assemble

- Steps 2--4 make `H^2(U)` finite.
- `U = K^` (Step 1). `K` has (T), so `K^ab` is finite.
- Step 0 then says `H^2(K^) -> H^2(K; T)` is injective with image `R(K)`. This is (SF1), and
  `R(K)` is finite.

## The case that tells you something

Rerun Step 4 on `Z_p^2`, whose Lie algebra has `b_2 = 1` (artifact calibration).
- `H^2_c(Z_p^2, Q_p) = Q_p`, and the embedding into `H^3_c` fails.
- Indeed `H^2(Z_p^2, Q_p/Z_p)` contains `Q_p/Z_p`, and `R(Z^2) = Q/Z` is infinite.

The arithmetic input is the single number `b_2(sl_3) = 0`, together with van der Kallen's finite
`H_2` at the primes not dividing the level. Neither input sees the archimedean part of
`H^2(K; T)`, which is invisible in finite dimensions by Step 0.
