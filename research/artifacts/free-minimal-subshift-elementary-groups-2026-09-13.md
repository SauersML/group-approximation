# Elementary groups over free minimal Z^d subshift algebras; presented crossed products are SFTs

Lane `ex-fp-kazhdan-ring`, 2026-09-13. Unreviewed. Part 3. Parts 1–2:
- `research/artifacts/sft-crossed-product-presentation-rigidity-2026-09-13.md`;
- `research/artifacts/free-minimal-crossed-product-rings-and-permutive-rigidity-2026-09-13.md`.

Setting. `q` is a prime power, `X ⊆ A^(Z^d)` a free minimal subshift, `(σ^g x)(h) = x(h + g)`,
`R = LC(X, F_q) ⋊ Z^d` with `u^g f u^(-g) = f o σ^g`, and `τ^g := σ^(-g)`, so that
`u^g chi_Y u^(-g) = chi_(τ^g Y)`. Norms are sup norms. `G = EL_3(R)`.

## 1. Theorem A (the Z^d version of the Pestov 9.1 group)

**Theorem A.** `S = G/Z(G)` is an infinite simple Kazhdan group, and it is `F_q`-linear sofic.
Every normal subgroup of `G` is central or equal to `G`. `Z(G) ⊆ F_q^x 1_3`.

- **The case `d = 1`.** This is the reviewed theorem of
  `research/artifacts/simple-kazhdan-lef-subshift-elementary-group-2026-09-12.md`, where `S` is
  moreover LEF.
- **The case `d >= 2`.** No LEF or sofic certificate is claimed. For shifts of finite type without
  finite orbits, exact periodic models are unavailable (peer Theorem A in
  `research/artifacts/fp-simple-amenable-z2-sft-2026-09-12.md`).

*Proof.*
- **Kazhdan.** `R` is generated as a ring by `u_i^(±1)`, the letter cylinders and a primitive
  element. So it is finitely generated, and `elementary-groups-over-fg-rings-have-property-t`
  applies.
- **Infinite.** `e_12(LC(X, F_q)) <= G`.
- **Linear sofic.** Part 2, Propositions 2 and 3.
- **Centre.** Part 2, Proposition 1.
- **Simplicity.** Section 2 below transcribes Section 4 of the reviewed artifact. Each step is
  restated with the changes it needs.

## 2. Root detection with boxes

**2.1 Long cylinders have long return times.** For every `L` there is `k_L` such that every
cylinder `C = {x : x|_(B_k) = v}` with `k >= k_L` satisfies `σ^g C ∩ C = ∅` for `0 < |g| <= L`.

*Proof.* Suppose not. Then there are patterns `v_k` of radius `k -> ∞` and some fixed `g` with
`0 < |g| <= L`, together with points `x_k` whose pattern at `0` and at `g` is `v_k`. Such an `x_k`
is `g`-periodic on `B_(k - L)`. Limit points of the `x_k` are `g`-periodic, which contradicts
freeness. Every clopen set is a finite union of cylinders of any large radius.

**2.2 Tower subrings.** Let `U` be clopen with `σ^g U ∩ U = ∅` for `0 < |g| <= 2m`. For clopen
`W ⊆ U` and `a, b ∈ B_m` put

```text
E_ab(W) = chi_(τ^a W) u^(a-b) = u^(a-b) chi_(τ^b W).
```

The levels `τ^b U`, `b ∈ B_m`, are pairwise disjoint. Hence
`E_ab(W) E_cd(W') = u^(a-b) chi_(τ^b W) chi_(τ^c W') u^(c-d) = delta_bc E_ad(W ∩ W')`.
The span `B_m(U)` is a subring, isomorphic to `M_(|B_m|)(LC(U, F_q))`, with unit
`chi_V` where `V = ⊔_(a ∈ B_m) τ^a U`.

**2.3 Absorption.** Suppose `σ^g U ∩ U = ∅` for `0 < |g| <= 2(m + w)`, `r` and `r'` have
propagation `<= w` (`f_g = 0` for `|g| > w`), and `b ∈ B_m(U)`. Then `r b r' ∈ B_(m+w)(U)`.

*Proof.* Take `r = f u^i`, `b = E_ab(W)`, `r' = f' u^j`. Then
`r b r' = f chi_(τ^(a+i) W) (f' o σ^(i+a-b)) u^(i+a-b+j)`. Split `W` into clopen pieces `W_k` on
whose `τ^(a+i)`-translates `F = f · (f' o σ^(i+a-b))` is constant, equal to `c_k`. This gives
`sum_k c_k E_(a+i, b-j)(W_k)`, with `|a+i|, |b-j| <= m + w`.

**2.4 Level ideals.** For `N ⊴ G`, `I(N) = {a : e_12(a) ∈ N}` is a two-sided ideal. The proof is
unchanged: commutator identities and signed permutations. Since `R` is simple, `I(N) != 0` forces
`N = G`.

**2.5 A noncommuting localized root.** Let `g ∈ N ⊴ G` be noncentral, let `w` bound the propagation
of the entries of `g^(±1)`, and put `L = 2w + 3`.
- Let `Σ_L` be the set of `λ chi_C` and `λ chi_C u^(±e_i)`, over cylinders `C` of radius `>= k_L`.
  It generates `R` as a ring: cylinders of a fixed large radius partition `X`, and
  `u^(e_i) = sum_C chi_C u^(e_i)`.
- `{s : g commutes with every e_ij(s)}` is a subring. So some `h = e_ij(s)` with `s ∈ Σ_L` does not
  commute with `g`.
- Each such `s` lies in `B_1(U)`, with `U` a translate of `C`, and translates of `C` have return
  times `> L`:
  - `chi_C = E_00(C)`;
  - `chi_C u^(e_i) = E_(e_i, 0)(τ^(-e_i) C)`;
  - `chi_C u^(-e_i) = E_(-e_i, 0)(τ^(e_i) C)`.

**2.6 Localization.** Put `k = [g, h] != 1` and `m' = 1 + w`.
- The entries of `g h g^(-1) - 1` are `g_pi s (g^(-1))_jq`. They lie in `B_(m')(U)` by 2.3, since
  `2m' = 2w + 2 <= L`.
- So `k - 1` and `k^(-1) - 1` lie in `M_3(B_(m')(U))`, and `k = (1 - e) 1_3 + k_V` with
  `e = chi_V`, `V = V_(m')(U)`.
- Since `M_3(B_(m')(U)) ≅ LC(U, M_D(F_q))` with `D = 3|B_(m')| >= 27`, `k` is a locally constant
  `κ : U -> GL_D(F_q)` with `κ ≢ 1`.

**2.7 Case 1: `κ(x_0)` not scalar.**
- **The embedding.** Choose a clopen `W ∋ x_0` on which `κ = κ_0`. The unital map
  `M_D(F_q) -> M_3(B_(m')(W))`, `e_((p,a),(p',b)) -> E_ab(W) E_pp'`, gives an injective
  `ι_W : SL_D(F_q) -> G`.
  - A transvection with `p != p'` maps to a root element.
  - One with `p = p'` maps to the commutator `[e_pp''(x), e_p''p(y)]`, with `x = c E_ab(W)` and
    `y = E_bb(W)`.
- **Normal closure.** `ι_W^(-1)(N)` is normal and contains every `[κ_0, ε]`. It is noncentral, since
  `SL_D(F_q)` is perfect and `κ_0` is not scalar, so it is all of `SL_D(F_q)`, using `D >= 3`.
- **Conclusion.** Hence `e_12(chi_W) ∈ N`.

**2.8 Case 2: `κ = λ 1_D` with `λ ≢ 1`.** Then `k = c 1_3` with `c ∈ LC(X, F_q)^x`, where `c = 1`
off `V` and `c = λ` on the tower levels over each piece.
- **The root.** Choose a clopen `W ⊆ U` with `λ = λ_0 != 1` on `W`, and put
  `r = chi_Y u^(e_1)` with `Y = τ^((m'+1) e_1) W`. Then `r != 0`, and `Y ∩ V = ∅`, because
  `(m'+1) e_1 ∉ B_(m')` and return times exceed `L`.
- **Twisting.** `c r c^(-1) = c chi_Y (c^(-1) o σ^(e_1)) u^(e_1)`. On `Y`, `c = 1`, and
  `σ^(e_1) Y = τ^(m' e_1) W ⊆ V`, where `c = λ_0`. So `c r c^(-1) = λ_0^(-1) r`.
- **Conclusion.** `[k, e_12(r)] = e_12((λ_0^(-1) - 1) r) ∈ N` is a nonzero root.

**2.9 Conclusion.** A noncentral normal subgroup contains a nonzero root, so it is `G` by 2.4.
`Z(G) ⊆ F_q^x 1_3` by part 2, Proposition 1. So `S` is simple. QED

## 3. Finitely presented crossed products of subshifts are of finite type

**Proposition B.** Let `X ⊆ A^(Z^2)` be a subshift, `k` a field, and suppose `R_X = LC(X, k) ⋊ Z^2`
is finitely presented. Then `X` is an SFT.

*Proof.*
1. **Local presentations.** Define `A_D` as in part 1, Section 1, with `L(X)` in (R4). Lemma 1 of
   part 1 holds verbatim for any subshift. So `A_D = R_X` for some `D`.
2. **A commutative representation.** Let
   `Y_D = {y : every B_D-pattern of y occurs in X}`.
   `A_D` acts on finitely supported functions `Z^2 -> ℓ(Y_D)`: at site `w`, `e_a` acts by
   `[y(w) = a]` and `u^g` by translation. All operators at one site are diagonal, so (R2)–(R4) hold.
3. **Descent.** This representation factors through `R_X`, so it kills `p_π` for every pattern `π`
   not occurring in `X`, of any radius. So no `y ∈ Y_D` contains such a `π`, and `Y_D ⊆ X`.
4. **Conclusion.** Also `X ⊆ Y_D`, so `X = Y_D` is of finite type. QED

**Corollary.** Among Cantor `Z^2`-systems, those with finitely generated crossed products are the
expansive ones, the subshifts. Those whose crossed product is simple and finitely presented are
exactly the free minimal quantum rigid SFTs. For the "only if" direction, a simple crossed product
forces a minimal and topologically free action. A topologically free minimal `Z^2`-subshift of
finite type is free: finite orbits are excluded by minimality, and points with a rank-one
stabilizer are recalled, not re-checked, to have a closed invariant orbit closure contradicting
minimality. That recalled step is flagged.

## 4. The gates after Theorem A

Put `Ω` a free minimal quantum rigid SFT, if one exists, and `R = R_Ω`, `S_n = EL_n(R)/Z`.
- **(a)** `R` is finitely presented (part 1, Theorem 1).
- **(b) Open.**
  - Krstić–McCool (JPAA 141 (1999), Theorem 3, quoted in
    `research/artifacts/khanh-2609-08428-leavitt-gl-verified-2026-09-11.md`) gives `St_n(R)`
    finitely presented for `n >= 4`. So `S_n` is finitely presented iff
    `ker(St_n(R) -> S_n)` is finitely normally generated.
  - Heuristic only, not verified here: iterated twisted Bass–Heller–Swan for the regular ring
    `LC(Ω, F_q)` suggests `K_2(R) ≅ Z ⊕ H^1(Z^2; LC(Ω, F_q^x))` up to extension, which is finitely
    generated when the tiling cohomology is. The unstable kernel, its centrality, and stability
    ranges were not checked.
- **(c) Open.**
  - `S_n` is `F_q`-linear sofic.
  - Soficity would follow from Arzhantseva–Păunescu Question 8.5 for `S_n`, or from
    `fg-simple-weakly-sofic-groups-are-sofic` through `linear-sofic-implies-weakly-sofic-over-every-field`.
  - The graph's monomial-to-Hamming bridge (`monomial-rank-models-are-hamming-models`) needs monomial
    models. The Følner models of root elements `1 + f u^g E_ij` are not monomial.
