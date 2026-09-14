# SK review 8, part 2: character rigidity of G_X, and EL_2 over every finite field

Lane `sk-verify-8`, 2026-09-13. This covers priority items 3–4 of the revision-4 candidates. No other verifier had
reviewed these nodes. Every step was re-derived on paper. Notation follows the owners' artifacts.

## 0. Verdicts

| Node (owner, landing) | Verdict |
|---|---|
| `subshift-tower-unit-group-characters-are-constant` + route (sk-characters-rigidity-b, d78467369d) | PASS; note N2 |
| `subshift-elementary-groups-are-character-rigid` + route | PASS; note N3 |
| `subshift-elementary-groups-have-trivial-irs` + route | PASS (principle re-derived in §3) |
| `subshift-el-2-simple-modulo-centre-every-finite-field` + route (sk-el2-fq, fa92d5adcb) | PASS. Items 1–2 are unconditional. Item 3: (T) and finite generation rest on `complementary-full-idempotents-make-el-2-kazhdan` (sk-verify-4 PASS line on main), and LEF on `minimal-subshift-algebra-is-simple-lef-ring` item 3 (not re-checked here) |

No FAIL, no GAP.

## 1. Tower unit groups (artifact part 1)

- **GNS.** `τ` is a normal trace on `M = π(G)''`, and it is faithful: `τ(x*x) = 0` gives `‖xπ(g)ξ‖² = τ(x*x)` by
  traciality, and `ξ` is cyclic.
- **Matrix units.** `E^C_{ab}E^{C′}_{a′b′} = e_{T^a(C ∩ T^{a′−b}C′)} u^{…}`. For `j = a′−b ∈ (−H_C, H_{C′})` the sets
  `C` and `T^jC′` are distinct levels unless `C = C′` and `j = 0`. So `A(𝒫) ≅ ⊕_C M_{H_C}(F_2)`, and `Σ E^C_{aa} = 1`.
- **Nesting.**
  - `B_n ⊆ B_{n−1}`, and the itinerary through levels of `𝒫_{n−1}` is constant on bases. So towers of `𝒫_n` are
    concatenations of towers of `𝒫_{n−1}`.
  - `T^aC = ⨆_{passages} T^{c+a}C′` gives `E^C_{ab} = Σ E^{C′}_{c+a,c+b}`: a unital block-diagonal inclusion.
- **Lemma 1.**
  - (i) Cross-block transvections are `e_pq(E^C_{ab})`, and in-block ones are commutators through `p′ ≠ p`.
  - (ii) No periodic points and `B_n ↓ {y}` give return times `≥ J` eventually.
  - (iii) `X = ⋃_{i<L}T^{−i}C_0`, so every `L` consecutive orbit points meet `C_0`. Each visit starts a full `C_0`-block
    of the concatenation, and the itinerary is constant on `C′`. So there are at least `⌊H_{C′}/L⌋` passages.
  - **PASS.**
- **Lemma 1′ (support ≥ ⌊H/L⌋).**
  - `h[C′]` is block diagonal with the block `h[C]` on each passage.
  - For `λ ∈ F̄_2`, `h[C_0] − λ ≠ 0`: `h[C_0] = λI` with `F_2`-entries forces `λ ∈ {0,1}`, and both are excluded.
  - So each `C_0`-passage costs at least 1 in `dim ker(h[C′] − λ)`, and `supp(h[C′]) ≥ #passages ≥ ⌊H_{C′}/L⌋`. **PASS.**
- **Lemma 2 (two points generate).**
  - The set of `r` with every `e_ij(r) ∈ ⟨L_y, L_{y′}⟩` is a subring containing `1 = e_X` and every `e_D`.
  - `u = ue_{X∖T^{−1}B_n} + ue_{T^{−1}B_n}`. The first summand is `Σ E^C_{a+1,a}` over non-top levels of `𝒫_n`.
  - Once `B′_m ∩ B_n = ∅` and `T^{−1}B_n` is a union of `𝒫′_m`-levels, those levels avoid the top levels `T^{−1}B′_m`.
    So the second summand is `Σ E′_{a+1,a}`.
  - `u^{−1}` is symmetric, using base levels. **PASS.**
- **Lemma 3 (the Larsen–Tiep application).**
  - `GL_N(F_2) = SL_N(F_2)` is simple for `N ≥ 3`, so Theorem A (quoted verbatim, arXiv:2403.09046) applies.
  - Class size: `dim C(x) = Σ_λ Σ_k (μ′_{λ,k})² ≤ Σ_λ (dim E_λ)(mult_λ) ≤ (N − supp x)N`. The centralizer is cut out by
    `F_2`-linear equations, so its `F_2`-dimension is the same.
  - `|GL_N(F_2)| ≥ 2^{N²}/4` (product ≈ 0.289). So `log|x^G|/log|G| ≥ α − 2/N² ≥ α/2` when `N² ≥ 4/α`.
  - Degree: a faithful representation restricted to the unipotent radical `F_2^{⌊N²/4⌋}` has characters that span its
    dual, so `χ(1) ≥ ⌊N²/4⌋`.
  - Then `|χ(x)|/χ(1) ≤ χ(1)^{−cα/2} ≤ ⌊N²/4⌋^{−cα/2}`. **PASS.**
- **Lemma 4 (constancy).**
  - `χ|_{L_n}` is a convex combination of normalized irreducible characters, with trivial weight `τ(p_{L_n}) ↓ τ(p_{L_y})`.
  - A nontrivial `ρ = ⊗ρ_{C′}` has a nontrivial factor, and every other factor ratio has modulus `≤ 1`.
  - Once `H_{C′} ≥ 4L`, `supp(h[C′]) ≥ H_{C′}/L − 1 ≥ 3H_{C′}/(4L) = N/(4L)`. So the ratio is at most
    `δ_{1/(4L)}(3·min H_C) → 0`.
  - `e_12(e_P) ∈ L_y ∖ 1` for every nested system, so `c` is independent of all choices. **PASS.**
- **N2 (route display).** In `subshift-tower-unit-group-characters-are-constant-proof` step 2, "If `h_{C_0} ≠ 1`" should
  read "If `h[C_0] ≠ 1`" (the component of `h`, not the tower height).

## 2. The central trivial part and the Bessel step (artifact part 2)

- **Lemma 5.**
  - `|A_n| = 2^{#levels} → ∞` and `τ(p_{A_n}) = (1 + (|A_n|−1)c)/|A_n| → c`. The same holds for `L_n`.
  - `p_{L_y} ≤ p_A` with equal traces, so they are equal by faithfulness. The same holds at `y′`.
  - So `π(x)p_A = p_A` on `L_y ∪ L_{y′}`, hence on `G` (Lemma 2). Adjoints give `p_Aπ(x) = p_A`, so `p_A` is central.
  - **PASS.**
- **Lemma 6 (a) local constants.**
  - For small `V`, `g_pq e_V = Σ_a γ_a e_{T^aV}u^a`, because `f∘T^a` is constant on `V`.
  - The constants are unchanged on a nonempty clopen `V′ ⊆ V`, so triviality is inherited both ways.
  - A partition into small sets shows that `g ≠ 1` has a nontrivial small set.
- **(b) noncommuting roots.** If `g` commutes with every `e_ij(e_V)`, then `g_pi e_V = 0` (`p ≠ i`), `e_V g_jq = 0`
  (`q ≠ j`), and `g_ii e_V = e_V g_jj`.
  - The `u^a`-coefficients with `a ≠ 0` sit on the disjoint sets `T^aV` and `V`, so they vanish.
  - So `ge_V = diag(ε)e_V`, and invertibility gives `ε_i = 1`. So `V` is trivial.
- **(c) one tower group.**
  - `f u^a e_V f′ u^b = f e_{T^aV}(f′∘T^{−a})u^{a+b} ∈ {0, ε_{a,−b}}`, so `g^{−1}xg − I_3 ∈ ψ_V(M_d)`.
  - `x² = 1` gives `A² = 0`, so `g^{−1}xg = I − e + ψ(I_d + A) ∈ H_V`.
- **(d) disjoint towers.**
  - `ψ_V(M_d)ψ_{V′}(M_d) = 0` in both orders, so `H_V` and `H_{V′}` commute and meet trivially.
  - `ε_{ab} ∈ A(𝒫_n)` at `y*`: for `v ∈ V`, `T^bv` and `T^av` lie in the same tower at levels differing by `a − b`
    exactly when no point strictly between them, in orbit order, lies in `B_n`. That holds since `B_n ∩ T^cV = ∅` for
    `|c| ≤ w`.
  - **PASS.**
- **(e)–(g).**
  - Points with pairwise disjoint segments exist (no periodic points, `V` infinite). Shrinking gives `V_k` with disjoint
    towers and one `y*` outside all of them.
  - `x_l` and `g^{−1}x_kg` commute, so `g^{−1}ygy^{−1} = (g^{−1}x_lg·x_l)(g^{−1}x_kg·x_k)`. The second factor is nontrivial
    and `H_{V_l} ∩ H_{V_k} = 1`, so the product is `≠ 1` and lies in `L_{y*}`.
  - So the `v_k` are orthonormal, `⟨ξ,v_k⟩ = conj χ(g)`, and Bessel gives `K|χ(g)|² ≤ 1`. **PASS.**
- **Theorem R.**
  - `c = 1` gives `p_A = 1`, so `χ ≡ 1`.
  - Otherwise `χ_2 = τ((1−p_A)π(·))/(1−c) = ⟨π(·)(1−p_A)ξ,(1−p_A)ξ⟩/(1−c)` is a character, `χ = c + (1−c)χ_2`, and
    `χ_2 = 0` on every `L_y ∖ 1`. **PASS.**
- **N3 (display).** Lemma 6's hypothesis should read "for every nested system at every `y`". §6 supplies exactly that,
  because Lemma 4 holds for every nested system with the same `c`.

## 3. Invariant random subgroups

The principle (artifact `leavitt-irs-rigidity-from-character-simplex-2026-09-08.md` §1) is re-derived here, not read:
- For an IRS `μ`, `χ_μ(g) = μ{H ∋ g} = ∫⟨λ_{G/H}(g)δ_H, δ_H⟩dμ` is a character. So `μ{H ∋ g} = b` for `g ≠ e`.
- Take `ν` symmetric, lazy, with full support on the countable `G`, and `M = Σν(g)π(g)`.
  - On the GNS side, `Σ_g ν^{*n}(g)χ_μ(g) = b + (1−b)ν^{*n}(e) → b`, since `G` is infinite.
  - Pointwise, `ν^{*n}(H) = ⟨M^nδ_H,δ_H⟩_{ℓ²(G/H)} → 1/[G:H]` if the index is finite and `→ 0` otherwise.
  - With no proper finite-index subgroups the limit is `[H = G]`. Dominated convergence gives `μ({G}) = b`.
- So `μ{H ∋ g, H ≠ G} = 0` for every `g ≠ e`, and countability gives `μ = bδ_G + (1−b)δ_1`.
- The inputs are that `G_X` is infinite and simple, and Theorem R. **PASS.**

## 4. EL_2 over every finite field (sk-el2-fq artifact §2–§4)

- **Lemma C.**
  - Commuting with `I + E_12` and `I + E_21` gives `g = cI_2`.
  - `[c, e_U] = Σ_j c_j(e_{T^jU} − e_U)u^j`. Evaluating at `x ∈ U` with `T^{−j}x ∉ U` kills `c_j`, `j ≠ 0`.
  - `cu = uc` makes `c` invariant, so constant, and `λ ≠ 0`. **PASS.**
- **Step 1.**
  - Small sets partition every clopen set, and `e_ij` is additive.
  - Commuting with all `e_ij(e_V)`, `e_ij(e_Vu)` for small `V` gives `e_12(1)`, `e_21(1)`, `e_12(u)` and every `e_12(e_U)`.
    Lemma C then makes `g` central. **PASS.**
- **Step 2 (product formula with shift `c`, top-level column).**
  - `(fu^i)(e_Vu^c)(f′u^j) = f e_{T^iV}(f′∘T^{−i−c})u^{i+c+j} = μ ε_{i,−(c+j)}`, since `f∘T^i` and `f′∘T^{−c}` are constant
    on `V` with `|i| ≤ w < m` and `|c| ≤ 1 ≤ m`. The second index lies in `[−m, w]`.
  - Entries: `X` has second index in `[−m, w]`; `Y = −ε_{0,−c}E_ij`; `XY` has second index `−c`; `YX` has second index `≤ w`.
  - `k − I = X + Y + XY` and `k^{−1} − I = −X − Y + YX` lie in `ψ(M_d)`, so `k ∈ H`.
  - No entry of `k − I_2` uses second index `m`. So the columns `(1,m)` and `(2,m)` of `A` vanish, and `κ` is not scalar
    unless `k = I`. **PASS.**
- **Step 3.**
  - `[k,S] ⊆ N ∩ S ⊴ S`. If `N ∩ S` were central, `σ ↦ [k,σ]` would be a homomorphism from the perfect `S` into
    `Z(S)`, so `κ` would centralize `SL_d(F_q)` and be scalar.
  - A noncentral normal subgroup `K` of the quasisimple `SL_d(F_q)`, `d ≥ 6`, satisfies `KZ = S`, so `S/K` is abelian
    and `K = S`. **PASS.**
- **Step 4 (Peirce propagation over `F_q`).**
  - `[I+x, I+y] = I+xy` whenever `x² = y² = yx = 0`: no signs and no hypothesis on `q`.
  - `J_AB` is additive because `E_BE_A = 0`.
  - The chain `J_13, J_12, J_32, J_31, J_23, J_21` spans each block by fullness of `E_1`, `E_2`, `E_3`.
  - `Y_AB ⊆ G` and the `Y_AB` generate. Re-derived: `I + zE_11 = [e_12(z), e_21(e′)]` for `z ∈ eRe′`, and `e_12(e′re′)`
    is a sum of `[I + e′aeE_12, I + ebre′E_22]` using `1 = Σ a_t e b_t`. **PASS.**
- **§4.**
  - The centre is finite, and `G` is infinite.
  - (T) comes from `complementary-full-idempotents-make-el-2-kazhdan`, and f.g. from (T) (BdlHV 1.3.1, recalled).
  - LEF: the unital embedding sends scalars to scalars; the finitely many `gg′^{−1} − λI_2 ≠ 0` stay nonzero ω-a.e.; the
    partial models into `PGL_{2N_k}(F_q)` preserve products modulo scalars. **PASS.**

## 5. Scope

- **Not re-read at source:** Larsen–Tiep Theorem A (the owner quotes it verbatim), BdlHV 1.3.1.
- **Not re-checked:** the import `minimal-subshift-algebra-is-simple-lef-ring` item 3.
- **Not searched:** novelty.
