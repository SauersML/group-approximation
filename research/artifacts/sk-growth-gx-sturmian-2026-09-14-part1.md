# sk-growth-gx-sturmian part 1: the matrix engine at its K-theoretic boundary (2026-09-14)

Lane sk-growth-gx-sturmian. Plan: `research/artifacts/sk-growth-gx-sturmian-plan-2026-09-14.md` (342494433e). Status: two established claims plus one literature import, all unreviewed. The Sturmian case of `every-subshift-elementary-group-non-uniform-growth` stays OPEN.

## 1. M1: matrix decompositions need a divisible unit
Claim `matrix-decompositions-of-subshift-rings-need-divisible-unit`. If `M_k(R_X) ≅ M_N(A)` for a unital ring `A`, then `k[χ_X] = N·c` in `K^0 = C(X,Z)/(1−T_*)C(X,Z)`, and `k/N ∈ μ(K^0)` for every invariant probability `μ`.
- **Proof.** The images `f_i` of the matrix units `E_ii` are pairwise equivalent orthogonal idempotents summing to 1, so `[1] = N[f_1]` in `K_0(M_k(R_X)) = K_0(R_X)`, where `[1_(M_k)] = k[1_R]`.
  - `K_0(R_X) ≅ K^0` with `[1] ↦ [χ_X]` (`subshift-crossed-product-k0-is-coinvariant-group`, PASS at group level).
  - Integration against `μ` kills coboundaries and sends `[χ_U] ↦ μ(U)`, so `k = N·μ(c)`.
- **Sturmian.** `μ(K^0) ⊆ Z + αZ` (clopen measures), so `k = 3`, `N = 3·2^n` forces `2^(−n) ∈ Z + αZ`, which gives `n = 0`.
- **Meaning.** The dyadic engine needs `EL_3(R_X) = EL_(3·2^n)(A)` through a ring decomposition. For Sturmian `X` there is none, at any scale, whatever `A` is.
- **Scope.** Non-standard group isomorphisms `EL_3(R_X) → EL_(3·2^n)(A)` are not excluded here. They would contradict standardness results of Petechuk/Bunina type, whose applicability in characteristic 2, rank 3 is not checked (compare `peirce-root-homomorphisms-of-e3-are-standard`).

## 2. G1: piecewise dyadic level models suffice
Claim `piecewise-dyadic-level-models-give-non-uniform-growth`; the route has the short form. Details:
- **(a) Matrix units.** Put `s_i = Σ_n u^n e_(A_n)` and `s′_i = Σ_n e_(A_n) u^(−n)`, with `A_n = A^(i)_n`.
  - `s′_i s_i = Σ_(m,n) e_(A_m) u^(n−m) e_(A_n) = Σ_(m,n) e_(A_m ∩ T^(n−m)A_n) u^(n−m)`. For `m ≠ n`, `A_m ∩ T^(n−m)A_n = T^(−m)(T^mA_m ∩ T^nA_n) = ∅`, so `s′_i s_i = Σ_n e_(A_n) = e_(W_1)`.
  - `s_i s′_i = Σ_n u^n e_(A_n) u^(−n) = Σ_n e_(T^nA_n) = e_(W_i)`.
  - Rewriting `s′_j = Σ_n u^(−n) e_(T^nA^(j)_n)` shows `s′_j = s′_j e_(W_j)`, and `s_i = e_(W_i) s_i`. So `s′_j s_i = 0` for `i ≠ j`.
  - Hence `ε_ij = s_i s′_j` satisfy `ε_ij ε_kl = δ_jk ε_il` and `Σ ε_ii = 1`, and `R ≅ M_(2^k)(ε_11Rε_11)`.
- **(b) Corner.** `e_W R e_W = {Σ_j f_j u^j : supp f_j ⊆ W ∩ T^jW}`.
  - Let `B_j = {x ∈ W : r_W(x) = j}` (finitely many `j`) and `v = Σ_j e_(T^jB_j)u^j`. Then `vv′ = v′v = e_W` with `v′ = Σ_j u^(−j)e_(T^jB_j)`, using that `T_W` permutes `W`.
  - `f 1_(W∩T^jW) u^j = Σ_m f 1_(C_(j,m)) v^m`, where `C_(j,m)` is the clopen set of `x ∈ W ∩ T^jW` whose orbit segment from `T^(−j)x` to `x` contains exactly `m` returns to `W`.
  - So `f ↦ f`, `u_W ↦ v` defines a surjection `LC(W,F_2) ⋊_(T_W) Z → e_WRe_W`. It is injective because the coefficient of each `v^m` is recovered by compressing with the clopen sets `C_(j,m)`. This is the ring form of the reduction `(X⋊Z)|_W ≅ W ⋊_(T_W) Z`.
- **(c) Generators.** Coding `x ∈ W` by its sequence of return words gives an injective equivariant continuous map into `𝒜_W^Z`. The alphabet `𝒜_W` is finite because return times are bounded, and injectivity holds because a subshift point is determined by its coordinates along the orbit.
  - The image is a minimal infinite subshift, hence aperiodic.
  - Entropy: `h_top(T_W) = sup_ν h_ν(T_W)`. The `T_W`-invariant probabilities are exactly `μ(· ∩ W)/μ(W)` for `T`-invariant `μ` (Kakutani), and Abramov gives `h_ν(T_W) = h_μ(T)/μ(W) = 0`.
  - `krieger-subshift-embedding-theorem` gives an equivariant embedding into `{0,1}^Z`. With `U` the preimage of the cylinder `[1]`, products of the `v^j e_U v^(−j)` and their complements give all cylinder indicators, so `Σ_k = {v, v^(−1), e_U}` generates `A_k`.
- **(d) Engine.** `EL_3(R) ≅ EL_(3·2^k)(A_k)` by (a) and sk-free-8 part 2 Lemma 4. Theorem B (`el-small-ball-generating-sets-from-grigorchuk-levels`, PASS) with `|Σ_k| = 3` and `m = 3` gives `γ(ℓ) ≤ exp(Cℓ^β)` for `ℓ ≤ 2^(⌊k/2⌋)/3` and all large `k`. Lemma 0 then gives `ω → 1` along the good `k`.
- **(e) Exponential growth.** (T) (EJZ) plus infiniteness gives non-amenability, hence exponential growth.

**What it contains.**
- Constant towers (`F_i = {i−1}`), so sk-free-8 Corollary A2 and the zero-entropy constant-length-2 substitutions.
- Every zero-entropy minimal subshift whose unit is `2^k`-divisible via clopen piecewise translations at infinitely many scales.
- Equivalence with plain `[1_X] ∈ 2^k K^0` would follow from realizing the class `[1_X]/2^k` by `2^k` clopen sets equivalent in the full pseudogroup (Glasner–Weiss 1995 Lemma 2.5, seen only as quoted in a survey: strict measure inequality gives `γ ∈ [[T]]` with `γ(B) ⊆ A`). The exhaustion argument is not written, so this equivalence is NOT claimed.

## 3. M2: why a remainder summand breaks the counting
- If `[χ_X]` is not `2^n`-divisible, write `M_3(R_X) = End(P^(m2^n) ⊕ Q)` with `[Q] = 3[χ_X] − m2^n[P] > 0`. This is possible: `K^0` is dense in its order for infinite minimal `T`, and internal cancellation holds (sk-algebraic-putnam, PASS).
- Generation of `EL` needs root elements `e_(p,q)(x)` and `e_(q,p)(y)`. Conjugates by level permutations give `e_(a,q)(x)` and `e_(q,b)(y)` for `a,b` in short inverted orbits, all sharing the single point `q`.
- Column-`q` conjugates commute with each other, and so do row-`q` conjugates. But `[e_(a,q)(x), e_(q,b)(y)] = e_(a,b)(xy)` for `a ≠ b`, a root element at a pair that is not separated.
- So `lem:commuting-supports` fails, the normal form `p_1p_2p_3p_4` does not close, and counting words of length `ℓ` in this subgroup has no subexponential bound.
- `Q` cannot be split into `2^n` equal pieces (its class is not divisible), nor made orthogonal to `P` (both are full in a simple ring).
- Dead at: the single defect point.

## 4. Firewall: is G1 strictly more than dyadic eigenvalues?
Test case `ζ: 0 ↦ 0010, 1 ↦ 01`.
- The incidence matrix `M = [[3,1],[1,1]]` is primitive, with `det = 2` and Perron eigenvalue `2+√2`, which is irrational, so the subshift is aperiodic.
- `M² = 2·[[5,2],[2,1]]`, so the lengths `|ζ^(2j)(a)|` are divisible by `2^j` and the unit is divisible by every `2^j` in `K^0`.
- Return words to `0` in the fixed point are `0` and `01`, with `|ζ^n(r)| ∈ 2^(⌊n/2⌋)Z`. Host's criterion for primitive substitutions (recalled, not re-read) then makes every `1/2^j` a continuous eigenvalue, so this example already has the dyadic odometer factor.
- No certified zero-entropy example with 2-divisible unit and no dyadic eigenvalue was found. Ormes-type strong orbit realizations exist in the Cantor-minimal category, but expansiveness and zero entropy were not checked.

## 5. Literature
- Krieger's embedding theorem: verbatim secondary statement from arXiv:2606.25475, Theorem 1 (web fetch of the HTML, 2026-09-14). Primary W. Krieger, ETDS 2 (1982) 195–202; Crossref check recorded in the landing message. The primary paper was not opened.
- Abramov's formula and the variational principle: recalled (textbook).
- Glasner–Weiss 1995 Lemma 2.5: quoted from a web survey result only; not used in any claim.

## 6. Next
- Sturmian `X`: the matrix route is closed by M1 and M2. Any proof must change the engine, for example an intermediate-growth level-permutation family on Rauzy level sets (owned by sk-rauzy-intermediate for `[[φ]]′`), transferred to matrices where the remainder summand appears as a second tower color.
- G1 strictness: certify an example (a weakly mixing zero-entropy minimal subshift with `Z[1/2] ⊆ K^0` unit-divisible), or prove that for subshifts 2-divisibility of the unit forces dyadic eigenvalues (unlikely in general).
