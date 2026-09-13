---
rg: 2
id: sp4-finite-index-multiplier-lazard-whitehead-proof
kind: route
title: Finite-dimensional classes are profinite, and sp4 has no second Lie algebra cohomology
target: sp4-finite-index-fd-projective-multiplier-is-finite
requires:
  - sp4-fd-projective-multiplier-is-finite
---

**Source checks** (PDFs fetched on MSI, pages read locally, 2026-09-12).

- Bass--Milnor--Serre, Publ. IHES 33 (1967), p. 129 (PDF p. 72).
  - The closure `Gamma^` of `Gamma` in the S-arithmetic completion "is
    just the profinite completion of `Gamma`".
  - Kneser's Strong Approximation Theorem, as quoted there: if `G` is
    simply connected, almost simple, not of type `E_8`, and `G(k_p)` is
    non-compact for some `p in S`, then `G_k` is dense in `G(A^S)`.
  - Theorem 14.1: the congruence subgroup conjecture holds for `Sp_2n`,
    `n >= 2`.  It asserts `C^S(G_k) = {1}` unless `S` is totally
    imaginary.
- Lazard, Publ. IHES 26 (1965), chapter V.
  - (2.2.2.2), (2.2.2.3), (2.2.3.1) and (2.2.3.2), pp. 165--166 (PDF
    pp. 162--163).  Every complete `p`-valued group `G` of rank `r` has a
    quasi-minimal complex `X_.`.  This is a split resolution of `Z_p` by
    filtered-free `Al G`-modules of ranks `C(r,n)`, and
    `H^n_c(G,M) = H^n(Hom_A(X_.,M))`.
  - (2.4.9), p. 178 (PDF p. 175).  For `G` complete `p`-valued of finite
    rank, `L = Q_p (x) (Lie Sat Al G)`, and `M` a complete topological
    `Q_p`-vector-space module, `H^*_c(G,M)` identifies canonically with
    `H^*(L,M)`.
  - (2.4.10)(iii), p. 179 (PDF p. 176).  The same holds after taking
    invariants, for any profinite `p`-adic analytic group.
- Whitehead's lemma `H^2(sp_4,Q) = 0` is model-tested by exact rank
  computation (artifact of the target claim).
- Classical and not re-read this session:
  - Malcev: finitely generated linear groups are residually finite.
  - Cohomology of a profinite group with discrete coefficients is the
    direct limit over finite quotients, with the Hochschild--Serre
    spectral sequence (Serre, Cohomologie galoisienne, I.2.2 and I.2.6).
  - Property (T) passes to finite-index subgroups and forces a finite
    abelianization.

Notation: `Gamma = Sp_4(Z)` and `Gamma(m) = ker(Gamma -> Sp_4(Z/m))`.
Profinite groups carry continuous cohomology with discrete
coefficients.  Undecorated `H^n(-)` means `H^n(-,Q/Z)`.

## Step 0: finite dimension means profinite

*Lemma.*  Let `Delta` be a finitely generated residually finite group.
Then `R(Delta)` is the image of `H^2(Delta^) -> H^2(Delta,T)`.  If
`Delta^ab` is finite, the map is injective.

*The image lies in `R`.*
- Take a finite quotient `q: Delta -> Q` and `b in Z^2(Q,mu_m)`.
- The twisted regular representation on `l^2(Q)` is
  `lambda_b(x) delta_y := b(x,y) delta_{xy}`.  By the cocycle identity,
  `lambda_b(x) lambda_b(x') = b(x,x') lambda_b(xx')`.
- So `lambda_b o q` realizes `inf [b]`.

*`R` lies in the image.*
- Let `pi: Delta -> U(d)` have cocycle `c`.  Rescale each `pi(g)` by a
  `d`-th root of `det pi(g)^(-1)` to get `u(g) in SU(d)`.
  - Then `u(g)u(h) = c'(g,h) u(gh)`.
  - Taking determinants forces `c' in mu_d`.
  - `[c'] = [c]` in `H^2(Delta,T)`.
- `E := {(g,x) in Delta x SU(d) : x in mu_d u(g)}` is a central extension
  `1 -> mu_d -> E -> Delta -> 1` of class `[c']`.
- `E` is residually finite, so some finite-index normal `N <| E` has
  `N cap mu_d = 1`.
  - `E` is finitely generated and lies in `Delta x pr_2(E)`.
  - The factor `pr_2(E) <= SU(d)` is finitely generated linear, hence
    residually finite (Malcev).
- Put `E_bar := E/N` and `Q := E/(N mu_d)`, a finite quotient of `Delta`.
  The map `E -> Delta x_Q E_bar` is an isomorphism.
  - Injective: `N cap mu_d = 1`.
  - Surjective: if `(g,y)` has matching images in `Q`, choose `e` over
    `g`.  Then `y = (eN) z` with `z in mu_d`, and `ez` maps to `(g,y)`.
- So `[c'] = inf_Q^Delta [E_bar]` comes from a finite quotient, and
  `H^2(Delta^) = colim_Q H^2(Q,Q/Z)`.

*Injective when `Delta^ab` is finite.*
- Let `b in Z^2(Q,mu_k)` with `inf b = delta f` for some `f: Delta -> T`.
  - Then `delta(f^k) = 1`, so `f^k` is a homomorphism `Delta -> T`.
  - Such a homomorphism factors through the finite group `Delta^ab`, so
    `f^k` has finite order `e` and `f` takes values in `mu_{ke}`.
- The map `s(g) := (q(g), f(g)^(-1))` is a homomorphism from `Delta`
  into the finite twisted product `Q x_b mu_{ke}`.
  - Its kernel `K` has finite index and lies in `ker q`.
  - `f` is constant on `K`-cosets.
- Over the finite quotient `Delta/K`, `inf b` is the coboundary of the
  induced `mu_{ke}`-valued function, so `[b]` dies in the colimit.

## Step 1: congruence completion

- By BMS Theorem 14.1 with `k = Q` and `S = {infinity}` (not totally
  imaginary), `C^S = 1`.
  - So `Gamma^` is the closure of `Gamma` in `Sp_4(A_f)`.
  - Every finite-index subgroup contains some `Gamma(m)`.
- By strong approximation, `Sp_4(Q)` is dense in `Sp_4(A_f)`.
  - `Sp_4(Z^)` is open and `Gamma = Sp_4(Q) cap Sp_4(Z^)`, so `Gamma` is
    dense in `Sp_4(Z^)`.
  - Hence `Gamma^ = Sp_4(Z^) = prod_p Sp_4(Z_p)`.
- For open `W <= Gamma^`, the closure of `Gamma cap W` is `W`.
- Choose `N` with `Gamma(N) <= Gamma'` and `v_p(N) >= 2` for every
  `p | N`.  If `Gamma(m) <= Gamma'`, take `N = m^2`.
- Put `U := Gamma'^`, the closure of `Gamma'`, which is open.
- Put `V := Gamma(N)^ = ker(Sp_4(Z^) -> Sp_4(Z/N))`, which splits as
  `V = K_S x G^S`:
  - `K_S = prod_{p|N} K_p`,
  - `K_p := ker(Sp_4(Z_p) -> Sp_4(Z/p^{v_p(N)}))`,
  - `G^S := prod_{p not| N} Sp_4(Z_p)`.
- `V` is open and normal in `U`.

## Step 2: Hochschild--Serre bookkeeping

For a closed normal `B <| A`, the `E_2^{2,0}`, `E_2^{1,1}` and
`E_2^{0,2}` terms bound the graded pieces of `H^2(A)`:

```text
|H^2(A)| <= |H^2(A/B,Q/Z)| . |H^1(A/B,H^1(B))| . |H^2(B)|.        (HS)
```

*Every `H^1` term is finite.*
- `H^1(V)` embeds, by restriction to the dense subgroup, in
  `Hom(Gamma(N),Q/Z)`.  That group is finite, since `Gamma(N)` has
  property (T).
- `H^1` of any direct factor of `V` embeds in `H^1(V)` through the
  projection.
- If `P` is such a factor and `M` is a finite abelian group, then
  `Hom(P,M)` is finite.  Indeed `M` embeds in some `(Q/Z)^r`, so
  `Hom(P,M)` embeds in `H^1(P)^r`.

*Apply (HS) twice.*
- `A = U`, `B = V`.  `U/V` is a finite group, so the first two factors
  are finite.  It remains to bound `H^2(V)`.
- `A = V = K_S x G^S`, `B = G^S`.
  - `K_S` acts trivially on `H^1(G^S)`, so
    `E_2^{1,1} = Hom(K_S, H^1(G^S))`, which is finite.
  - It remains to bound `H^2(K_S)` and `H^2(G^S)`.
  - `K_S` is a finite product, and the same argument reduces it to the
    `K_p`.

## Step 3: almost all primes, from level one

- `Sp_4(Z^) = (prod_{p|N} Sp_4(Z_p)) x G^S`, and the projection onto
  `G^S` has a section.  So inflation `H^2(G^S) -> H^2(Sp_4(Z^))` is
  injective.
- `Sp_4(Z^) = Gamma^`, and `Gamma^ab` is finite.  So Step 0 embeds
  `H^2(Gamma^)` in `H^2(Gamma,T)` with image `R(Gamma)`.
- `R(Gamma)` is finite by `sp4-fd-projective-multiplier-is-finite`.
  Hence `H^2(G^S)` is finite.

## Step 4: the finitely many primes, Whitehead through Lazard

Fix `p | N`, `K := K_p` and `v := v_p(N) >= 2`.  Then
`H^2(K) = (+)_l H^2(K, Q_l/Z_l)`.

*`l != p`.*
- `K` is pro-`p`: the successive quotients of the congruence filtration
  are `p`-groups.
- `H^n(K,Q_l/Z_l)` is the colimit of `H^n(P,Q_l/Z_l)` over finite
  `p`-group quotients `P`.
- For `n >= 1` each of these is killed by `|P|`, which acts invertibly on
  an `l`-primary module.  So they all vanish.

*`l = p`.*
- `K` is a complete `p`-valued group of rank `10`, with
  `omega(g) := v_p(g - 1) >= v >= 2 > 1/(p-1)`.  Write `X = g - 1` and
  `Y = h - 1`.
  - `gh - 1 = X + Y + XY` and `h^(-1) - 1 = -h^(-1) Y`.  So
    `omega(gh^(-1)) >= min(omega(g), omega(h))`.
  - `[g,h] - 1 = g^(-1) h^(-1) (XY - YX)`, so
    `omega([g,h]) >= omega(g) + omega(h)`.
  - Let `omega(g) = j >= 2` and expand `g^p - 1`.  `pX` has valuation
    exactly `j + 1`.  The middle binomial terms have valuation
    `>= 1 + 2j`, and `X^p` has valuation `>= pj >= j + 2`.  So
    `omega(g^p) = omega(g) + 1`.
- `0 -> Z_p -> Q_p -> Q_p/Z_p -> 0` gives a short exact sequence of
  continuous cochain complexes.  It is surjective on cochains: a
  continuous map from compact `K^n` to discrete `Q_p/Z_p` is constant on
  the pieces of a finite open partition, so it lifts.  Hence

  ```text
  H^2_c(K,Q_p) --> H^2(K,Q_p/Z_p) --> H^3_c(K,Z_p)   is exact.
  ```

- The Lie algebra of `K` is `sp_4(Q_p)`.  By Lazard V (2.4.9) and
  Whitehead, `H^2_c(K,Q_p) = H^2(sp_4(Q_p),Q_p) = 0`.  So
  `H^2(K,Q_p/Z_p)` embeds in `H^3_c(K,Z_p)`.
- By Lazard V (2.2.2.2)--(2.2.3.2), `H^3_c(K,Z_p) = H^3(Hom_A(X_.,Z_p))`
  with `Hom_A(X_n,Z_p) = Z_p^{C(10,n)}`.  So it is a finitely generated
  `Z_p`-module.
- `H^2(K,Q_p/Z_p)` is torsion, so it embeds in the torsion of that
  module, which is finite.

## Step 5: assemble

- Steps 2--4 make `H^2(U)` finite.
- `U = Gamma'^` (Step 1).  `Gamma'` has property (T), so `Gamma'^ab` is
  finite.
- Step 0 identifies `R(Gamma')` with `H^2(U)`, proving `(FI1)`.

## The case that tells you something

Rerun Step 4 on `Z_p^2`, whose Lie algebra has `b_2 = 1` (artifact).
- `H^2_c(Z_p^2,Q_p) = Q_p`, and the embedding fails.
- `H^2(Z_p^2,Q_p/Z_p)` contains `Q_p/Z_p`.
- This matches `R(Z^2) = Q/Z`, the infinite rotation supply behind ISW
  Corollary B.

The whole proof turns on one number: `b_2(sp_4) = 0`.
