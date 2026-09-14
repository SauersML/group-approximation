# sk-orthogonality-o part 1: Singer identities make isomorphisms standard, and type-2 pieces are localized (2026-09-14)

Lane sk-orthogonality-o. Plan: `research/artifacts/sk-orthogonality-o-plan-2026-09-14.md`. Theorem A (§§0–3) is
PASS-WITH-FIXES by sk-verify-25a and, independently, by sk-verify-25b (`research/artifacts/sk-verify-25a-2026-09-14.md`,
`research/artifacts/sk-verify-25b-2026-09-14.md`). Their fixes A1–A3, W2, W3 and W5 are merged below
(sk-rigidity-merge, 2026-09-14). §4 (Theorem B, Lemma N, Corollary B′) and §5 are unreviewed and off the Theorem D chain.

## 0. Notation

- `X, Y` are infinite minimal subshifts, `R_Y = LC(Y,F_2) ⋊ Z`, `G_Y = EL_3(R_Y)`, `M = R_Y^3`, and `α: G_X → G_Y` is
  an isomorphism.
- `Q = GL_3(F_2) ⊇ F21 = ⟨c, s⟩`, with `c` a Singer cycle of characteristic polynomial `m(x) = x³+x+1`.
- `q_V`, `K_V = α(F21_V)`, `S_V = I + Σ_{k∈K_V} k`, `E3_V`, `G_V`, `L_V` are as in
  `research/artifacts/sk-normalizer-recognition-2026-09-14-part1.md`.
- `ind` is the index of `subshift-gl3-index-kernel-is-elementary-group` (O1, reviewed: sk-verify-18 part6 PASS).
- **Isotypic parts.** For a finite group `K` of odd order acting on `M` through `GL_3(R_Y)`, the central idempotents of
  the semisimple algebra `F_2[K]` map to commuting idempotents of `M_3(R_Y)`. So `M` is the direct sum of its
  `K`-isotypic parts, and each part is an `R_Y`-direct summand.
  - The simple `F_2[F21]`-modules are `1`, `2` (inflated from `C_3`, with `End = F_4`), `3` (natural) and `3*`.
  - `S_VM` is the sum of the `2`, `3`, `3*` parts of `K_V`, and `(I − S_V)M = Fix(K_V)`.
- **(Sing_V)** `α(c_V)³ + α(c_V) = S_V`.
- **(O′)** `S_X = I`.

**Lemma 0 (forms of Sing).** (Sing_V) holds iff `K_V` acts on `S_VM` with type `3` only. (Sing_X) and (O′) together
hold iff `m(α(c_X)) = 0`.

*Proof.*
- `F_2[C_7] = F_2 × F_8 × F_8`, with idempotents `ε_1`, `ε_a` (factor `x³+x+1`) and `ε_b` (factor `x³+x²+1`).
- Restricted to `⟨c⟩`, the types `1` and `2` lie in `ε_1`, `3` lies in `ε_a`, and `3*` lies in `ε_b`.
- `m(α(c_V))` acts as `1` on the `ε_1` part, as `0` on the `ε_a` part, and invertibly on the `ε_b` part, since `m` and
  `x³+x²+1` are coprime.
- `I + S_V` is `1` on type `1` and `0` on types `2, 3, 3*`. So `m(α(c_V)) = I + S_V`, which is (Sing_V) in
  characteristic 2, iff there is no type `2` and no type `3*`.
- The second statement is the case `V = X` together with the vanishing of the type-`1` part. ∎

## 1. Representation facts

Classes of `F21`: `1` (size 1), `3A` (14), `7A` (3), `7B` (3). Put `α_7 = ζ+ζ²+ζ⁴ = (−1+√−7)/2`.
- Brauer characters on `F21`:
  - `1 = (1,1,1,1)`;
  - `2 = (2,−1,2,2)`;
  - `3 = (3,0,α_7,ᾱ_7)`;
  - `3* = (3,0,ᾱ_7,α_7)`.
- Brauer characters on `Q`: `3 = (3,0,α_7,ᾱ_7)` and `8 = (8,−1,1,1)` on the classes `1A, 3A, 7A, 7B`.
- Both group algebras have exactly these simple modules. `Q` has four 2-regular classes and simple modules
  `1, 3, 3*, 8`, all over `F_2`.

**F1.** `8|_{F21} = 2 ⊕ 3 ⊕ 3*`. Indeed `(8,−1,1,1) = (2,−1,2,2) + (3,0,α_7,ᾱ_7) + (3,0,ᾱ_7,α_7)`, since
`α_7 + ᾱ_7 = −1`. Restriction to the semisimple `F_2[F21]` is determined by the Brauer character. So the Steinberg
module has no `F21`-fixed vector.

**F4.** `Ext¹_{F_2Q}(3,3) = 0` (and the same for `3*`).
- `3 ⊗ 3* = End(3) = F_2·I ⊕ sl_3`, because the trace splits off: `tr(I) = 3 = 1`.
- `sl_3` has Brauer character `(9,0,2,2) − (1,1,1,1) = (8,−1,1,1)`, using `α_7ᾱ_7 = 2`. This is the character of the
  simple module `8`, so `sl_3 ≅ 8`.
- So `Ext¹(3,3) = H¹(Q, 3*⊗3) = H¹(Q,F_2) ⊕ H¹(Q,8) = 0`: `Q` is perfect and `8` is projective (defect zero).

**F5.** Restrictions of `t ⊗ t′` to the diagonal `F21`:
- `3⊗3 = (9,0,α_7²,ᾱ_7²)`, and `α_7² = ᾱ_7 − 1 = α_7 + 2ᾱ_7`. So `3⊗3 → 3 ⊕ 3* ⊕ 3*`.
- `3⊗3* = 1 ⊕ 8 → 1 ⊕ 2 ⊕ 3 ⊕ 3*`.
- `2⊗3 = (6,0,2α_7,2ᾱ_7) → 3 ⊕ 3`.
- `2⊗2 = (4,1,4,4) → 1 ⊕ 1 ⊕ 2`.

## 2. The index kernel

**Lemma I.** Assume O1. Then `G_Y = ker(ind) ⊴ GL_3(R_Y)`, and every element of finite order of `GL_3(R_Y)` lies in
`G_Y`. In particular `I + n ∈ G_Y` whenever `n² = 0`.

*Proof.* `ind` is a homomorphism to `Z`, so it kills torsion. In characteristic 2, `(I+n)² = I`. ∎

## 3. Theorem A: Singer identities make `α` standard

**Theorem A.** Assume O1, (Sing_V) for every clopen `V`, and (O′). Then:
- (O) holds;
- there are `k ∈ GL_3(R_Y)` and a Boolean subalgebra `𝔅′ ≅ LC(X,F_2)` of `R_Y` with `α(L_X) = k·GL_3(𝔅′)·k^{-1}`;
- `inn(k^{-1})∘α` maps every root subgroup `A_ij(R_X)` onto `A_ij(R_Y)`.

So `α` is standard: `inn(k^{-1})∘α = M_3(φ)|_{G_X}` for a ring isomorphism `φ: R_X → R_Y` (Fix W3), and `X` and `Y`
are strongly orbit equivalent.

*Proof.*
1. **(O).** Let `V ∩ W = ∅`.
   - `K_V × K_W` acts on the summand `S_VS_WM` with types `(t,t′)`, `t,t′ ≠ 1`. By (Sing_V) and (Sing_W) only `(3,3)`
     occurs.
   - `S_VS_W` commutes with `K_{V⊔W}`, the diagonal. By F5 the diagonal acts there as `3 ⊕ 3* ⊕ 3*`, so `S_VS_WM`
     contains a `3*` part of `K_{V⊔W}`.
   - (Sing_{V⊔W}) forbids that, so `S_VS_W = 0`.
2. **Module type.**
   - `M` is the union of the finite-dimensional `F_2[Q_X]`-submodules `F_2[α(Q_X)]m`.
   - A composition factor `1`, `3*` or `8` of such a submodule restricts to `F21_X` with a constituent `1`, `3*`, or
     `2` (F1), since restriction is exact (restriction to `F21_X` is semisimple since 21 is odd, so this constituent is
     a summand of `M` under `K_X`; Fix A3). These are forbidden by (O′) and (Sing_X).
   - So all factors are `3`, and by F4 every such submodule is semisimple. So `M` is semisimple of type `3`, and
     evaluation `3 ⊗_{F_2} P → M`, with `P = Hom_{Q_X}(3, M)`, is an isomorphism of `F_2[Q_X] ⊗ R_Y^op`-modules.
3. **Coordinates.**
   - `P³ ≅ R_Y³`, so `P` is finitely generated projective, and `3[P] = 3[R_Y]` in `K_0(R_Y) ≅ C(Y,Z)/(1−T_*)` (PASS),
     which is torsion-free. So `[P] = [R_Y]`.
   - By Theorem DP (`cantor-crossed-product-idempotents-similar-to-clopen-ones`, PASS), `P ≅ ⊕_{i≤3} e_{W_i}R_Y` with
     `Σ_i[1_{W_i}] = [1_Y]`.
   - **Division (Div).** H. Matui, "Approximate conjugacy and full groups of Cantor minimal systems",
     arXiv:math/0404224, Lemma 2.5, verbatim: "(1) [1_U] = [1_V] in K^0(X,α) if and only if there exists γ ∈ [[α]] such
     that γ(U) = V. (2) [1_U] ≤ [1_V] in K^0(X,α) if and only if there exists γ ∈ [[α]] such that γ(U) ⊂ V." It is
     stated there as a consequence of the Bratteli–Vershik model (Herman–Putnam–Skau); read on arXiv 2026-09-14, and
     read again at source by sk-verify-25a and sk-verify-25b (e-print l.272–283, numbering checked).
     - Put `W′_1 = W_1`. Since `[1_{Y∖W_1}] − [1_{W_2}] = [1_{W_3}] ≥ 0`, (2) gives `γ ∈ [[T]]` with
       `W′_2 := γW_2 ⊆ Y∖W_1`.
     - `W′_3 := Y∖(W′_1 ⊔ W′_2)` has class `[1_{W_3}]`, so (1) gives `W′_3 ~ W_3`.
     - `e_WR_Y ≅ e_{γW}R_Y` through the unit of `γ`, so `P ≅ ⊕_i e_{W′_i}R_Y = R_Y`.
   - So `M ≅ F_2³ ⊗ R_Y = R_Y³`, intertwining `α(Q_X)` with the constants: there is `k ∈ GL_3(R_Y)` with
     `α′ := inn(k^{-1})∘α` satisfying `α′(q_X) = q`. By Lemma I, `α′` maps `G_X` onto `G_Y`.
4. **Scalar supports.**
   - `S′_V := k^{-1}S_Vk` commutes with `α′(F21_V)` and with `α′(F21_{X∖V})`, so with the constant `F21`.
   - The span of the constant `F21` is `M_3(F_2)` (the cyclic algebra `F_8 ⋊ Gal`), whose commutant is `R_Y·I`.
   - So `S′_V = b_VI` with `b_V` an idempotent. By Proposition F (PASS) with (O) and (O′), `V ↦ b_V` is a Boolean
     embedding. Put `𝔅′ = span{b_V}`. (Fix W5: "Proposition F" means items 1–2 of Proposition F in
     `research/artifacts/sk-normalizer-recognition-2026-09-14-part1.md` §3, stated as item 3 of the node
     `frobenius-support-idempotents-give-boolean-realization`.)
5. **The diagonal.**
   - (Fix A2.) By (O) and (O′), `S_{X∖V} = I − S_V`. `α(Q_V)` commutes with `K_{X∖V}`, so it preserves `S_VM` and
     `(I−S_V)M = Fix(K_V)`. The kernel of its action on `Fix(K_V)` is normal in `α(Q_V) ≅ GL_3(2)`, which is simple, and
     contains `K_V ≠ 1`. So `α(q_V) − I = S_V(α(q_V) − I)S_V`, and conjugating by `k` gives `α′(q_V) − I ∈ b_VM_3b_V`.
     Likewise, with `X∖V` in place of `V`, `α′(q_{X∖V}) − I ∈ (1−b_V)M_3(1−b_V)`. Inside Theorem D, Theorem C of part 2
     gives this corner form directly.
   - Their product is `q`, the cross term vanishes, and so `α′(q_V) = I + b_V(q−I)`.
   - `L_X` is generated by the `q_V`, so `α′(L_X) = GL_3(𝔅′)`, and `α′(A_ij ∩ L_X) = T_ij(𝔅′) := {I + bE_ij : b ∈ 𝔅′}`.
6. **Roots.**
   - (Fix W2.) `C_{G_X}(A_ij ∩ L_X) = C_{G_X}(A_ij(R_X))`. Indeed, commuting with `I + fE_ij` for every `f ∈ D_X` forces
     `g_pi = 0` for `p ≠ i`, `g_jq = 0` for `q ≠ j`, and `g_ii f = f g_jj`. So `g_ii = g_jj` lies in
     `C_{R_X}(D_X) = D_X`, and it is an invertible idempotent, hence 1. By item 2 of
     `el3-root-subgroups-are-bicommutant-closed` (PASS), `C_{G_X}C_{G_X}(A_ij ∩ L_X) = A_ij(R_X)`.
   - Apply `α′`: `α′(A_ij(R_X)) = CC(T_ij(𝔅′)) ⊆ CC(A_ij(R_Y)) = A_ij(R_Y)`, because `T_ij(𝔅′) ⊆ A_ij(R_Y)` and
     `Z(R_Y) = F_2`.
   - So `α′(A_ij(R_X)) = I + J_ijE_ij` for additive subgroups `J_ij ∋ 1`. From `[e_ij(a), e_jk(b)] = e_ik(ab)`,
     `J_ijJ_jk ⊆ J_ik`, and with `1 ∈ J_jk` all `J_ij` equal one subring `J`.
   - `G_Y = α′(G_X)` is generated by the `e_ij(J) ⊆ M_3(J)`, so `e_12(r) ∈ M_3(J)` for every `r`, and `J = R_Y`.
7. **Standardness (Fix W3).** Write `α′(e_ij(r)) = e_ij(φ_ij(r))`. By Step 6 each `φ_ij: R_X → R_Y` is an additive
   bijection, and `φ_ij(1) = 1` because `α′` fixes the constant `e_ij(1)`. From `[e_ij(r), e_jk(s)] = e_ik(rs)` we get
   `φ_ik(rs) = φ_ij(r)φ_jk(s)`. Taking `s = 1` and `r = 1` gives `φ_ik = φ_ij = φ_jk`, so all `φ_ij` equal one ring
   isomorphism `φ: R_X → R_Y`. Then `α′ = M_3(φ)|_{G_X}`, since both are homomorphisms agreeing on generators. So
   `α = inn(k)∘M_3(φ)`, `R_X ≅ R_Y`, and `cantor-crossed-product-matrix-ring-iso-forces-soe` with `m = 1` gives strong
   orbit equivalence. (`peirce-root-homomorphisms-of-e3-are-standard` gives the same with `a_ij = E_ij`.) ∎

**Model tests.**
- `α = id`: `m(c_V) = e_{X∖V}I = I + S_V`.
- `α = inn(d)`, `d = diag(u,1,1)`: `m(dc_Vd^{-1}) = d·e_{X∖V}I·d^{-1} = I + S_V`, so Sing holds; `k = d`, `b_V = e_V`.
- **Graph automorphism** `γ_X(g) = (g*)^{-1}`: `γ_X(c_V)` has type `3*`, so Sing fails. Theorem A applies to `α∘γ_X`.
- **Natural ⊕ trivial fake:** fails (O′).
- **Steinberg fake** (8-dimensional module): its type-2 part violates Sing, by F1.
- **Remark.** Step 6 replaces maximal commutativity of `𝔅′`, which Theorem R assumes, by generation. So (Max) of the
  plan is not needed.

## 4. Theorem B: type-2 pieces are localized

*Unreviewed. Theorem C of part 2 supersedes this section, and Theorem D does not use it (sk-verify-25a, sk-verify-25b).*

For `∅ ≠ V ≠ X` put:
- `E_V = I − S_V`, the projection onto `Fix(K_V)`;
- `ε_V = Σ_{i<7} α(c_V)^i`, the projection onto `Fix(α(c_V))`;
- `P′_V = ε_V − E_V`, the type-2 part of `K_V`.

`kE_V = E_Vk = E_V` for `k ∈ K_V`, so `E_V ≤ ε_V` and `P′_V` is an idempotent.

**Lemma N (X-side).** `G_{X∖V} ⊴ C_{G_X}(c_V)`.

*Proof.* `Fix(c_V) = e_{X∖V}M_X` and `[M_X, c_V] = e_VM_X`, since `c − I` is invertible on `F_2³`. So `g ∈ C_{G_X}(c_V)`
commutes with `e_VI`, and conjugation by `g` preserves `I + M_3(e_{X∖V}R_Xe_{X∖V})`. ∎

**Theorem B.** Assume O1. If `E_V ≠ 0` and `P′_V ≠ 0`, then `A := α(G_{X∖V})` acts trivially on `ε_VM`. So
`P′_VM` has type `(2,1)` for `K_V × K_{X∖V}`, and the diagonal `K_X` has a type-2 part there.

*Proof.*
- `A` commutes with `α(c_V)` and with `K_V` (C2, PASS), so it commutes with `ε_V`, `E_V` and `P′_V`.
- Let `n = E_VyP′_V` with `y ∈ M_3(R_Y)`. Then `n² = 0`, and `α(c_V)n = n = nα(c_V)`, since `α(c_V)` is the identity on
  `ε_VM`. So `h = I + n ∈ C_{G_Y}(α(c_V))` by Lemma I.
- By Lemma N, transported, `hAh^{-1} = A`. For `g = I + z ∈ A`:
  - `hgh^{-1} = I + z + E_V(yz + zy)P′_V`, because `P′_VE_V = 0` and `z` commutes with `E_V, P′_V`.
  - This commutes with `P′_V` only if `E_V(yz+zy)P′_V = 0`. So `n·zP′_V = zE_V·n` for every `n ∈ E_VM_3(R_Y)P′_V`.
- Replacing `n` by `nx` with `x ∈ P′_VM_3P′_V` gives `n[x, zP′_V] = 0`.
  - `M_3(R_Y)` is simple and `E_V ≠ 0`, so `E_VM_3P′_V` has zero right annihilator in the corner.
  - So `zP′_V` is central in `P′_VM_3(R_Y)P′_V`, whose centre is `F_2P′_V`.
  - `g` is invertible on `P′_VM`, so `zP′_V = 0`.
- Then `zE_V·E_VM_3P′_V = 0`, and fullness of `P′_V` gives `zE_V = 0`. ∎

**Corollary B′.** Assume O1. If `K_X` has no type-2 part (for instance under (Sing_X)) and `Fix(K_V) ≠ 0`, then `K_V`
has no type-2 part.

## 5. What remains

*Superseded: part 2 proves (O′), the absence of type-2 parts and constant orientation (Theorem C, Corollaries O′ and
T), and (Div) was checked at source by sk-verify-25a and sk-verify-25b. The list below is the original plan, kept as a
record.*

- **(O′) and the type-2 part of `K_X`** (top level). Next: the centralizer `C_{G_X}(c_X) = (F_8 ⊗ R_X)^× ∩ G_X` has no
  normal corner subgroup, and the same radical trick should be run against it.
- **`Fix(K_V) = 0`** for proper `V`. Next: conjugate `V` into `X∖V` with scalar units from `[[T]]′`.
- **Orientation (`3*` parts).** Mixed `(3,3*)` pieces are excluded by (O′) and F5; `(3*,3*)` and `(3,3)` pieces are
  excluded by Sing; the remaining case is a clopen-wise mixture, for the `psq` argument of Theorem R Step 5(iii).
- **(Div).** Check it at source.
