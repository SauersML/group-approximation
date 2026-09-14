# sk-open-4 dictionary, part 2: rational spectrum, factors, invariant measures, and finite rank

Lane sk-open-4, 2026-09-13. Unreviewed until a verifier PASSes it. The setting is as in part 1.

## 1. Theorem E (rational spectrum ⟺ matrix-ring structure)
Let (X,T) be an infinite minimal Cantor system, q a prime power, R_X = LC(X,F_q) ⋊_T Z, and p ≥ 2. The following are equivalent:
1. e^{2πi/p} is a continuous eigenvalue of (X,T);
2. there is a clopen U with X = U ⊔ TU ⊔ … ⊔ T^{p−1}U;
3. [χ_X] ∈ p·K^0(X,T);
4. M_p(F_q) embeds unitally in R_X;
5. R_X ≅ M_p(S) for some unital ring S.

**Moreover, under (2):**
- R_X ≅ M_p(R_{(U,T^p)}), and (U,T^p) is an infinite minimal Cantor system (a subshift over p-blocks if X is a subshift);
- EL_n(R_X) ≅ EL_{np}(R_{(U,T^p)}) for every n ≥ 1;
- SL_{np}(F_q[t,t^{-1}]) ≤ EL_n(R_X).

Over F_2 with n = 3: G_X ≅ EL_{3p}(R_{(U,T^p)}), and G_X contains the S-arithmetic lattice SL_{3p}(F_2[t,t^{-1}]).

**Proof.**
- **(1)⇒(2).**
  - Let f be a continuous eigenfunction. |f| is invariant, so it is constant; normalize |f| = 1.
  - f^p is invariant, so it is a constant c. So f takes the p values ζλ^a with ζ^p = c and λ = e^{2πi/p}.
  - U = f^{-1}(ζ) is clopen, and f∘T = λf gives T^aU = f^{-1}(ζλ^a).
- **(2)⇒(1).** Put f = λ^a on T^aU.
- **(2)⇒(4),(5).**
  - Put E_ab = χ_{T^aU} u^{a−b} for 0 ≤ a,b < p.
  - Then E_ab E_cd = χ_{T^aU ∩ T^{a−b+c}U} u^{a−b+c−d}. This is δ_bc E_ad, because |b − c| < p and the levels are disjoint. Also Σ_a E_aa = 1.
  - So R_X ≅ M_p(E_00 R_X E_00).
  - χ_U u^j χ_U = χ_{U ∩ T^jU} u^j vanishes unless p | j, and T^{pk}U = U. So the corner is {Σ_k f_k u^{pk} : f_k ∈ LC(U,F_q)} = LC(U,F_q) ⋊_{T^p} Z.
  - **(U,T^p) is minimal.** If C ⊆ U is closed and T^p-invariant, then C ⊔ TC ⊔ … ⊔ T^{p−1}C is closed and T-invariant, so it is X. Since T^iC ⊆ T^iU and the levels are disjoint, C = U.
- **(4)⇔(5).** This is standard: a full set of p×p matrix units gives R ≅ M_p(e_11 R e_11).
- **(5)⇒(3).**
  - Matrix units give orthogonal, pairwise equivalent idempotents e_1, …, e_p with sum 1. So [1] = p[e_1] in K_0(R_X).
  - By `subshift-crossed-product-k0-is-coinvariant-group`, the isomorphism K_0(R_X) ≅ K^0(X,T) sends [1] to [χ_X].
- **(3)⇒(1).**
  - Write χ_X = p h + g − g∘T^{-1} with h, g ∈ C(X,Z). Reduce mod p to get ḡ(Tx) − ḡ(x) = 1 in Z/p.
  - Then f = λ^{ḡ} is continuous and satisfies f∘T = λ f.
- **Groups.**
  - EL_n(M_p(S)) = EL_{np}(S) inside GL_{np}(S). A block elementary matrix is a product of elementary matrices at distinct positions. Conversely, an elementary matrix inside one block is a commutator of block elementaries through a second block.
  - The cyclic partition is a factor map X → Z/p. Pulling back, R_{Z/p} ↪ R_X unitally.
  - Applying the matrix-unit construction to Z/p itself gives R_{Z/p} ≅ M_p(F_q[u^{±p}]).
  - Since F_q[t^{±1}] is Euclidean, EL_{np}(F_q[t^{±1}]) = SL_{np}(F_q[t^{±1}]). ∎

**Factors in general.** A factor map π: (X,T) → (Y,S) of Cantor systems gives an injective unital equivariant ring map h ↦ h∘π on LC(·,F_q). It extends to R_Y ↪ R_X, so EL_n(R_Y) ≤ EL_n(R_X). With Y = {pt}, SL_n(F_q[t^{±1}]) ≤ EL_n(R_X) always.

**Model tests.**
- **Sturmian X_α.** It has no rational eigenvalues, and indeed [1] = 1 is not p-divisible in Z + αZ ✓.
- **Toeplitz subshift with skeleton periods p^k.**
  - It has the eigenvalues e^{2πi/p^k}, so R_X ≅ M_{p^k}(S_k) and G_X ≅ EL_{3p^k}(S_k) for every k.
  - Its K^0 contains Z[1/p] ∋ [1]/p^k ✓.
- **p = 1** is vacuous ✓.

**Reading.** The rank 3 in G_X is not an invariant of the family: rational spectrum converts G_X into higher-rank elementary groups over induced systems.

## 2. Theorem M (invariant measures ⟺ rank length functions from the note's finite models), q = 2
Let (y_k) be periodic words of periods N_k → ∞ with the same (2k+1)-words as X, as in the note, and let ν_k be their periodic empirical measures.
- **(a)** If ν_k → μ weak*, then for every matrix M over R_X the normalized ranks of the note's models D_{y_k}(M) converge to
  `rk_μ(M) = lim_L (1/L) Σ_{v ∈ L_{L'}(X)} μ[v]·rank(M on the window v)`,
  where L' = L + 2(ρ + w) and ρ, w bound the windows and exponents of M.
- **(b)** rk_μ is a Sylvester matrix rank function with rk_μ(χ_U) = μ(U), affine in μ.
  - For ergodic μ it is the Ara–Claramunt measure rank function, by their uniqueness (`cantor-z-crossed-product-embeds-in-continuous-factor`).
  - It is faithful, because minimal X gives μ full support.
- **(c)** Every invariant probability μ arises as such a limit. Choose the words from μ-generic segments that begin with a fixed 2k-word v and are followed by v, concatenating segments for convex combinations; joins at v create no new words. Then take weak* limits diagonally.
- **(d)** ℓ_μ(g) = rk_μ(g − I_3) is a conjugation-invariant length function on G_X, with ℓ_μ(gh) ≤ ℓ_μ(g) + ℓ_μ(h), ℓ_μ(g^{-1}) = ℓ_μ(g), and ℓ_μ(g) = 0 iff g = 1. Since ℓ_μ(e_12(χ_U)) = μ(U), the map μ ↦ ℓ_μ is injective and affine.

**Proof of (a).**
- Cut Z/N_k into consecutive blocks of length L. Zeroing the entries that couple different blocks changes the rank by at most 3·2w·(N_k/L + 1).
- The rank of each block is a function of the word of y_k on the block, widened by ρ + w on each side. That word lies in L(X), since every window of y_k is a word of X.
- Averaging over the L cutting offsets gives rank D_{y_k}(M)/N_k = Σ_v ν_k[v]·rank_v/L + O(w/L).
- Let k → ∞, then L → ∞. The O(w/L) bound makes the limit exist and equal rk_μ(M). The Sylvester axioms pass to limits of normalized ranks along the partial homomorphisms. ∎

**Credit.** The existence and uniqueness of the rank function is Ara–Claramunt (arXiv:1902.06476). New here, and bounded: these rank functions are exactly the limits of the note's LEF models, and each gives a faithful bi-invariant length on G_X.

## 3. Open (finite rank): is EL_n(R_X) a Steinberg group?
**Claim, OPEN.** For n ≥ 5 (and at n = 3?), EL_n(LC(X,F_2)⋊Z) ≅ St_n(LC(X,F_2)⋊Z), so H_2(EL_n(R_X);Z) = 0.

Attempts:
- **Stable K_2 vanishes** for every Cantor homeomorphism (part 1, Theorem S). Injective stability for K_2 (van der Kallen), K_2(n,R) → K_2(R) injective in a range n ≥ sr(R) + c, would give K_2(n,R_X) = 0 and so St_n(R_X) ≅ EL_n(R_X).
  - This needs a finite stable-rank bound for R_X, which is the target of sk-stable-rank-a/b.
  - St_n(R) is centrally closed for n ≥ 5 (Kervaire), which would then give H_2 = 0.
  - Dies at: sr(R_X) is unknown here.
- **Ranks 3 and 4 over F_2-algebras carry exceptional multipliers.** SL_3(F_2) and SL_4(F_2) ≅ A_8 have Schur multiplier Z/2. So no low-rank claim is made without a proof.
- **Homology stability for H_3** (van der Kallen) would make H_3(EL_n(R_X)) ≅ K^0(X,T)/3 for large n, under the same stable-rank dependence.
