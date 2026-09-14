# sk-first-order plan: the first-order theory of G_X (2026-09-14)

Lane sk-first-order, wave 12. Main tip at planning time: `d97dfb2a62`.

Throughout `X` is an infinite minimal subshift over a finite alphabet `A`, `R = R_X = LC(X,F_2) ⋊_T Z`, and `G = G_X = EL_3(R) = E_3(R)`. `S = {1, u, u^{-1}} ∪ {e_a : a ∈ A}` is the note's finite generating set of `R` as a unital ring.

## 0. Why now
`sk-free-3` (plan §5) left the model theory of `G_X` as a secondary target and named the one obstacle: *"the G ↔ R bi-interpretation needs definable matrix entries without bounded elementary generation. That is a real obstacle."*

That obstacle is gone. `subshift-el-groups-boundedly-elementary-generated` (sk-free-6 Theorem D, PASS-WITH-FIXES twice: sk-verify-15 §1, sk-verify-16 §1) says

> every `h ∈ G` is a product of at most 78 elementary matrices in a **fixed** sequence of positions, so `G = e_{i_1j_1}(R) ⋯ e_{i_78j_78}(R)`.

An existential formula with 78 ring variables therefore defines `G` inside `M_3(R)`. This lane cashes that in.

## 1. Lemma Z (established here). `Z(R) = F_2`.
Let `z = Σ_j f_j u^j` be central.
- `zu = uz` gives `f_j = f_j∘T^{-1}`, so each `f_j` is a `T`-invariant clopen function, hence constant by minimality: `f_j = c_j ∈ F_2`.
- For `f ∈ LC(X,F_2)`, `zf = Σ_j c_j (f∘T^{-j}) u^j` and `fz = Σ_j c_j f u^j`. So `c_j ≠ 0` forces `f∘T^{-j} = f` for every `f`, i.e. `T^j = id`. As `X` is infinite and minimal, `T` is aperiodic, so `c_j = 0` for `j ≠ 0`.

So `Z(R) = F_2`, and `Z(R)^× = {1}`. ∎

Model test: for `X` a single periodic orbit of period `p`, `u^p` is central, and the argument correctly fails at aperiodicity.

## 2. Lemma C (established here). Root subgroups are definable with finitely many parameters.
Write `U_ij = {e_ij(r) : r ∈ R}`. Then, in `G`,

    U_13 = C_G( {e_12(s) : s ∈ S} ∪ {e_23(s) : s ∈ S} ),
    U_12 = C_G( {e_13(s) : s ∈ S} ∪ {e_32(s) : s ∈ S} ),
    U_23 = C_G( {e_13(s) : s ∈ S} ∪ {e_21(s) : s ∈ S} ),

and each right-hand side is a centralizer of an explicit finite subset of `G`, so each `U_ij` is definable in `G` with `2|S|` parameters.

*Proof for `U_13`* (the others are the same computation after a permutation of coordinates). `g ∈ GL_3(R)` commutes with `e_12(r)` iff `g·rE_12 = rE_12·g`, i.e.

    g_{i1} r = 0 (i ≠ 1),    r g_{2j} = 0 (j ≠ 2),    g_{11} r = r g_{22}.

Take `r = 1 ∈ S`: `g_{21} = g_{31} = 0`, `g_{23} = 0`, `g_{11} = g_{22}`. Commuting with `e_23(1)` gives likewise `g_{12} = g_{32} = 0` and `g_{22} = g_{33}`. So `g = cI + g_{13}E_{13}` with `c := g_{11} = g_{22} = g_{33}`. The remaining conditions for general `s ∈ S` read `cs = sc`, so `c` commutes with every element of `S`, hence with all of `R`, so `c ∈ Z(R) = F_2` by Lemma Z. Invertibility forces `c = 1`, i.e. `g = e_13(g_{13}) ∈ U_13`. Conversely `U_13` centralizes `U_12 ∪ U_23`, because `E_13E_12 = E_12E_13 = E_13E_23 = E_23E_13 = 0`. ∎

Both inclusions are computed in `GL_3(R)`, so the identity holds with `C_G` on the left.

## 3. Lemma W. Permutation parameters.
In characteristic 2, `e_23(1)e_32(1)e_23(1)` is the permutation matrix `P_{23}` of the transposition `(2 3)`, and likewise `P_{12} = e_12(1)e_21(1)e_12(1)`. Both lie in `G`, they generate the full permutation group of the three coordinates inside `G`, and conjugation by `P_σ` sends `e_ij(r)` to `e_{σ(i)σ(j)}(r)`. So for every pair `i ≠ j` there is an explicit `w_{ij} ∈ G` with `w_{ij} U_13 w_{ij}^{-1} = U_{ij}` and `w_{ij} e_13(r) w_{ij}^{-1} = e_{ij}(r)`. ∎

## 4. Theorem T1 (established here). `R` is interpretable in `G` with parameters.
Domain: `U_13`, definable by Lemma C. The bijection is `e_13(r) ↔ r`.
- **Addition** is the group operation: `e_13(r)e_13(s) = e_13(r+s)`.
- **Multiplication**: with the parameters of Lemma W, for `a = e_13(r)` and `b = e_13(s)`,

      [ w_{12} a w_{12}^{-1} , w_{23} b w_{23}^{-1} ] = [e_12(r), e_23(s)] = e_13(rs).

- **0** is the identity, **1** is the parameter `e_13(1)`.

So `R` is interpreted in `G` on a definable set with definable operations, using the parameter list `p̄ = ( e_12(s), e_23(s), e_13(s), e_21(s), e_32(s) for s ∈ S ; P_12, P_23 )`, all of them explicit words in the generators of `G`. ∎

## 5. Theorem T2 (established here). `G` and `R` are bi-interpretable with parameters.
**(a) `G` is interpretable in `R`, with no parameters.** Interpret `M_3(R)` as `R^9` with the usual definable operations. By Theorem D,

    G = { M ∈ R^9 : ∃ r_1 … r_78,  M = ê_{i_1j_1}(r_1) ⋯ ê_{i_78j_78}(r_78) },

with the positions `(i_k,j_k)` fixed once and for all. This is an existential formula, so `G` is a definable subgroup of `GL_3(R)` and the group operation is definable. ∎

**(b) The composite on the `R` side is definable.** `R → (G interpreted in R) → (R interpreted in that G)` is `r ↦ e_13(r) ↦ r`, and its graph `{(r,M) : M = ê_{13}(r)}` is definable in `R`. ∎

**(c) The composite on the `G` side is definable — this is where Theorem D is essential.** Let `R^*` be the copy of `R` interpreted in `G` by T1, and let `G^*` be the copy of `G` interpreted in `R^*` by (a). Define

    Θ(g, M) :⟺ ∃ a_1 … a_78 ∈ U_13 [ g = ∏_k w_{i_kj_k} a_k w_{i_kj_k}^{-1}  ∧  M = ∏_k ê_{i_kj_k}(a_k) ],

where the first product is taken in `G` and the second in the interpreted matrix ring over `R^*`.
- `Θ` is definable in `G` with the parameters of T1 and Lemma W.
- **Total**: Theorem D gives `g = ∏_k e_{i_kj_k}(r_k)`, and `a_k := e_13(r_k)` works.
- **Single-valued**: under `R^* ≅ R`, `∏_k ê_{i_kj_k}(a_k)` corresponds to the actual matrix `∏_k e_{i_kj_k}(r_k) = g`. So `M` is the matrix of `g`, whatever tuple is chosen.
- **Injective**: `G ⊆ GL_3(R)` is a group of matrices, so `g` is its matrix.
- **Surjective onto `G^*`** and multiplicative, by Theorem D applied to `gh`.

So `Θ` is a definable isomorphism `G → G^*`, and with (b) the pair `(G,R)` is bi-interpretable with parameters. ∎

**What breaks without Theorem D.** Without a bound, `E_3(R)` is only the union over `n` of the products of `n` elementary matrices, which is not first-order in `R`, and the tuple `(a_k)` in `Θ` has no fixed length. That is exactly the obstacle recorded in sk-free-3 §5(iii).

## 6. Consequences to prove next (targets, not yet claims)
- **T3.** `Th(G_X) ≡_T Th(R_X)`, and `Th(G_X)` is hereditarily undecidable.
  - Needs: `C_R(u) = F_2[u^{±1}]` (immediate from minimality, as in Lemma Z), plus the classical undecidability of the theory of `F_q[t]` or of `F_q[t,t^{-1}]`. **IMPORT TO CHECK AT SOURCE** (Penzin 1973 for `F_q[t]`; Denef 1979 for the existential theory). Also to check: that interpretability *with parameters* preserves hereditary undecidability (Ershov–Lavrov–Taimanov–Taitslin).
- **T4.** `R_X` is interpretable in `(N,+,·,L(X))` without parameters: code `r ∈ R` by a radius, a `u`-degree bound and a table on words, and read equality and the ring operations off `L(X)`. This direction looks routine.
- **T5 (the prize).** The converse, `(N,+,·,L(X))` interpretable in `R_X` with parameters. The missing piece is a definable coding of finite words: the cylinder idempotents `c_v = ∏_{t<m} u^{-t} e_{v_t} u^t` satisfy `v ∈ L(X) ⟺ c_v ≠ 0`, so `L(X)` is definable once the map `v ↦ c_v` is. This is the standard Gödel-coding step and is the real work.
- **T6.** With T4 + T5: `Th(G_X) ≡_T Th(N,+,·,L(X))`, so `G_X ≡ G_Y` forces `L(X)` and `L(Y)` to have the same arithmetic theory. And when `L(X)` is **recursive** — the Fibonacci/Sturmian case of the note's Corollary 5 — the predicate is arithmetically definable, so `G_X` would be bi-interpretable with `N` itself, hence QFA and prime by Nies. **IMPORT TO CHECK AT SOURCE** (Nies, *Describing groups*, BSL 13 (2007); whether his hypothesis allows parameters).
  - That would read: *for every infinite minimal subshift with recursive language, `G_X` is an infinite simple Kazhdan LEF group determined among finitely generated groups by a single first-order sentence.*

## 7. Firewalls and model tests
- Lemma Z, hence Lemma C, hence everything, **fails for periodic `X`**: then `Z(R) ⊋ F_2` and `C_G(U_12 ∪ U_23)` is larger than `U_13`.
- Theorem D is stated for `EL_3` over `LC(X,F_2)⋊Z` with `X` a minimal Cantor system. T2 inherits exactly that hypothesis; no claim is made for `EL_2`, for other coefficient rings, or for the lamplighter hosts, where bounded elementary generation is not known.
- T1 and T2 use no soficity, no property (T) and no simplicity of `G`.
- `Z(G) = 1` is not needed as an input: `G` is a group of matrices, so `Θ` is injective by construction.

## 8. Deliverables
- This plan.
- Nodes (after grep; no interpretability node for these groups exists on main):
  - `subshift-el-group-interprets-its-crossed-product-ring` (+ `-proof`), Theorems T1 and Lemmas Z, C, W;
  - `subshift-el-group-bi-interpretable-with-its-ring` (+ `-proof`), Theorem T2, requiring `subshift-el-groups-boundedly-elementary-generated`;
  - open claim for T5/T6.
- Review requests in `$SK2/queue/verify.txt`.
- Novelty: bounded check to be recorded with the claims. Bi-interpretability of a Chevalley-type group with its ring, via bounded elementary generation, is the Avni–Lubotzky–Meiri pattern for `SL_n(O)`; what is new here is that it applies to these simple Kazhdan groups at all, since the bounded generation input is itself new.
- **No note change proposed.** The paper is at rev4.3 and this is off its theme.
