# sk-verify-14, part 4: review of sk-free-8 (non-uniform exponential growth of elementary groups over self-similar rings) (2026-09-13)

Lane sk-verify-14, queue `sk/queue/sk-verify-13.txt`, lines 26–30.
- **Targets:** `research/artifacts/sk-free-8-nonuniform-growth-2026-09-13-part1.md` and `-part2.md`, with the claim and route nodes.
- **Method:** every step re-derived by hand, and the transfer checked line by line against the Sauer–Schesler e-print. No other review of these claims was on main when I started.

## 0. Verdicts

| claim | verdict |
|---|---|
| `el-small-ball-generating-sets-from-grigorchuk-levels` (Lemmas 1–3, Theorem B) | **PASS** |
| `self-similar-ring-elementary-groups-non-uniform-growth` (Lemma 4, Theorem A) | **PASS** |
| `constant-length-substitution-tower-partition` | **PASS, conditional on the literature import** `mosse-bilateral-recognizability` (Mossé not re-read; the elementary Thue–Morse proof re-derived) |
| `substitution-subshift-elementary-groups-non-uniform-growth` (Lemma 5, Corollary A1) | **PASS** (note N3) |
| `nonsofic-leavitt-el4-non-uniform-exponential-growth` | **PASS** |

No FAIL and no GAP.

## 1. Sources checked at source (MSI, 2026-09-13)
- **Sauer–Schesler, arXiv:2606.15945, e-print `nonuniformgrowth_hyp.tex`:**
  - `introtheorem` `thm: main estimate`, l.182–187: "There are constants $C>0$ and $\beta\in (0,1)$ and finite generating sets \(T_n\) of \(\Aut(F_{4\cdot 2^n})\) such that $\gamma^{T_n}(\ell)\le \exp(C \ell^\beta)$ for every $0\le \ell\le 2^{n/2}/3$";
  - `thm:G-subexponential` (l.418), `thm:BE` (l.451);
  - `prop:BE-finite` (l.463): for large n, ξ_n ∈ {ρ_n, η_n} and k ≤ r_n = 2^{⌊n/2⌋}, Δ ≤ Ck^α and N ≤ exp(Ck^α);
  - `lem:separation` (l.388): d(ρ_n,η_n) ≥ 2^{n−3} for n ≥ 4;
  - the inverted-orbit definition with right actions;
  - `lem:commuting-supports` (l.589), `lem:normal-form` (l.611), and the counting proof of the main estimate.
- **Sauer–Schesler, arXiv:2605.30163**, proof that W_n ≅ V: the linking graph on X_n with edges the 𝒢_n-translates of {θ_n, ρ_n} is K_{2^{n−1},2^{n−1}}, by 2-point homogeneity [Bekka–de la Harpe–Grigorchuk, Appendix A2].
- **N1 (credit locator).** The node calls the source "Theorem 2". In the e-print it is the second `introtheorem`, label `thm: main estimate`; its printed number was not checked.

## 2. Theorem B, the transfer from Aut(F_{4·2^n}) to EL_{m·2^n}(A)

| step | Sauer–Schesler | sk-free-8 | check |
|---|---|---|---|
| type 1 | truncated Grigorchuk generators on X_n × [4] | the same on X_n × [m] | involutions ✓ |
| type 2 | monomial group (Z/2)^4 ⋊ Sym(4) over η_n | Sym(m) permutation matrices over η_n | a group ✓ |
| type 3 | basis transposition (ρ_n,1) ↔ (θ_n,1) | its permutation matrix | involution ✓ |
| type 4 | Nielsen transvection λ_{(ρ_n,2),(ρ_n,3)} | e_{(ρ_n,2),(ρ_n,3)}(σ), σ ∈ Σ ∪ {1} | order 2 in characteristic 2 ✓ |
| generation | Nielsen generators (Lyndon–Schupp) | permutation matrices lie in EL(F_2); 2-transitivity; sums and commutators | ✓ |
| P_2 | (2^4·4!)^{Cℓ^α} | (m!)^{Cℓ^α} | ✓ |
| P_3 | word ũ = a_ng_1a_n ⋯ a_ng_ℓ | identical | ✓ |
| P_4 | exponents in [−ℓ,ℓ] at each point | coefficients in the F_2-span of Σ ∪ {1} | ✓ (additive group of characteristic 2) |

**Lemma 1 (generation).**
- [[0,1],[1,0]] = e_12(1)e_21(1)e_12(1) over F_2, so types 1–3 lie in EL.
- By transitivity, conjugates of the type-2 group give Sym({x} × [m]) for every x.
- Conjugates of τ_n give the edges of the connected linking graph on sheet 1, so the transposition graph on Y_n is connected and ⟨T_n⟩ ⊇ Sym(Y_n).
- 2-transitivity gives e_{yy′}(σ) for all y ≠ y′. The coefficient set {r : e_{yy′}(r) ∈ ⟨T_n⟩ ∀y≠y′} contains 1 and Σ and is closed under + (additivity) and · ([e_{yk}(r),e_{ky′}(s)] = e_{yy′}(rs), |Y_n| ≥ 3); negatives are themselves. So it is A.

**Lemma 2 (commuting supports).**
- The supports are over η_nh (type 2), {(ρ_ng,1),(θ_ng,1)} (type 3) and {(ρ_ng,2),(ρ_ng,3)} (type 4).
- Coincidence of base points forces d(ρ_n,η_n) ≤ 1 + 2r_n/3. For n = 5: 1 + 8/3 < 4; for n = 6: 1 + 16/3 < 8; the left side grows like 2^{n/2}, the right like 2^n. This contradicts separation.
- Types 3 and 4 use disjoint sheets.
- Type-4 conjugates at different base points have disjoint supports; at the same base point they commute because e_{yy′}(r)e_{yy′}(s) = e_{yy′}(r+s).

**Lemma 3 (normal form).** Write t_i = a_ig_i with at most one factor nontrivial. Then g_1⋯g_ℓ · a_1^{g_1⋯g_ℓ} ⋯ a_ℓ^{g_ℓ} = a_1g_1a_2g_2⋯a_ℓg_ℓ, by induction with x^g = g^{−1}xg. Every suffix has length ≤ ℓ ≤ r_n/3, so Lemma 2 separates the types, keeping the order within each type.

**Counting.**
- **P_1:** p_1 is the image of an element of 𝒢 of length ≤ ℓ, so |P_1| ≤ exp(C_1ℓ^γ).
- **P_2:** the type-2 conjugates live over 𝒪_{η_n}(u). At most exp(C_0ℓ^α) orbits, each of size ≤ C_0ℓ^α, and p_2 ∈ ∏_{x∈O} Sym({x}×[m]).
- **P_3:** the points ρ_ng_i⋯g_ℓ and θ_ng_i⋯g_ℓ are suffix points of ũ, which has length ≤ 3ℓ ≤ r_n, so `prop:BE-finite` applies. p_3 is a permutation of 𝒪_{ρ_n}(ũ)×{1}, giving exp(C(3ℓ)^α)·(C(3ℓ)^α)! ≤ exp(C_3ℓ^α log ℓ).
- **P_4:** p_4 = ∏_{x∈O} e_{(x,2),(x,3)}(r_x), with r_x in the F_2-span of Σ ∪ {1}.
- **Product:** the ball lies in P_1P_2P_3P_4, and for β ∈ (max{α,γ},1) the product is ≤ exp(Cℓ^β).
- **Uniformity:** C and β depend only on the Grigorchuk and Bartholdi–Erschler constants, |Σ| and m. The threshold on n (n ≥ 5 and that of `prop:BE-finite`) does not depend on A.

## 3. Theorem A (self-similar rings)
- **Lemma 4.** A block elementary matrix is a product of commuting elementary matrices across two blocks. An in-block e_ij(r) = [e_ik(r), e_kj(1)] with k in another block.
- **Scales.** R ≅ M_2(R) iterates to R ≅ M_{2^k}(R), and EL_n is functorial for ring isomorphisms. So EL_n(R) ≅ EL_{X_k×[n]}(R), where n ≥ 3 sheets suffice (type 3 on sheet 1, type 4 on sheets 2, 3).
- **Growth rate.** The preimages U_k of T_k(Σ) generate with k-independent constants, so ω(EL_n(R), U_k) ≤ exp(C(r_k/3)^{β−1}) → 1 by Fekete.
- **Exponential growth.** An infinite EL_n(R) over a finitely generated R has (T) (Ershov–Jaikin-Zapirain; required node `ejz-elementary-groups-explicit-kazhdan-constant` exists on main). An infinite Kazhdan group is non-amenable, and subexponential growth implies amenability.

## 4. Tower partition for constant-length substitutions
**The route's derivation from Mossé's two theorems, re-derived.**
- For constant length q the natural cutting points are E_1 = qN.
- **Cut status.** Declare position i of x ∈ X a cut if the window x[i−L, i+L], at any occurrence in u, sits at a rank in E_1. Bilateral recognizability makes this independent of the occurrence, and it is locally determined.
- **Cosets.** A window x[i−L, i+q−1+L] occurs in u at one rank. There the statuses of i and i+q agree, and positions i+1, …, i+q−1 are not cuts. So the cut set is a coset qZ + p(x), with p: X → Z/q continuous and p∘T = p − 1.
- **Partition.** V_0 = {p = 0} is clopen and X = ⊔_{k<q} T^kV_0.
- **ζ(X) ⊆ V_0.** Blocks of ζ(y) sit at qZ, and windows of ζ(y) come from ζ(u) = u at cut ranks.
- **V_0 ⊆ ζ(X).** Unique desubstitution gives y_k from a bounded window, and windows of y are desubstitutions of windows of u. So y ∈ X and ζ(y) = x.
- **Homeomorphism.** The inverse is locally determined, so continuous.

**The import.** `mosse-bilateral-recognizability` (Mossé, Bull. SMF 124 (1996), Theorems 1–2) is a literature import. The numdam PDF was fetched on MSI, but no text-extraction tool is available there, so the statements were NOT re-read.

**Thue–Morse proof, independent of Mossé, re-derived.**
- The language is overlap-free, so 000, 111, 01010 and 10101 never occur, and every window of length 5 contains 00 or 11.
- In a concatenation of 01 and 10 blocks these pairs occur only across block boundaries, so the phase is read from any length-5 window.
- Desubstitution is 01 ↦ 0, 10 ↦ 1, and long windows occur in u at phase-compatible positions.

For period doubling, the artifact's Corollary A2 (odometer factor) is an alternative route. It is artifact-only (§7).

## 5. Lemma 5 and Corollary A1
- **Matrix units.** With ε_00 = e_V, ε_11 = e_{TV} = ue_Vu^{−1}, ε_10 = ue_V and ε_01 = e_Vu^{−1}:
  - ε_10ε_01 = ue_Vu^{−1} = ε_11 and ε_01ε_10 = e_V;
  - ε_00ε_10 = e_Ve_{TV}u = 0;
  - ε_00 + ε_11 = 1 because X = V ⊔ TV.
- **Corner.** e_V(fu^k)e_V = f1_{V∩T^kV}u^k is 0 for odd k. T²V = V, so the corner is LC(V,F_2)⋊_{T²}Z with unit u²e_V.
- **Transfer.** A conjugacy (X,T) ≅ (V,T²|_V) induces R_X ≅ e_VR_Xe_V. With ζ from §4, R_X ≅ M_2(R_X).
- **Hypotheses.** R_X is generated by u^{±1} and the e_{[a]}, and G_X is infinite. Theorem A applies.
- **N3 (dependency, not a risk).** The route requires `finite-model-subshift-elementary-groups-simple-kazhdan-lef`, which has no review line on main, for simple/(T)/LEF. For infinite minimal subshifts these are the note's Theorem 1, which both rev3 referees re-derived. Primitive aperiodic substitution subshifts are infinite and minimal.

## 6. The Leavitt algebra
- **Matrix units.** s_it_j satisfy ε_ijε_kl = δ_jk ε_il (since t_js_k = δ_jk), and ε_00 + ε_11 = 1.
- **Corner isomorphism.** a ↦ s_0at_0: multiplicative (t_0s_0 = 1), unital onto ε_00, injective (t_0(s_0at_0)s_0 = a), and onto (ε_00xε_00 = s_0(t_0xs_0)t_0). So L ≅ M_2(L).
- **Hypotheses.** L is generated by 4 elements, has characteristic 2, and EL_n(L) is infinite. Theorem A gives non-uniform exponential growth for n ≥ 3.
- **Nonsoficity import.** The kernel-checked `universal-leavitt-el4-nonsofic` is over `BinaryLeavittAlgebra (ZMod 2)` (`GroupApproximation/Leavitt/UniversalLeavitt.lean` l.17), defined as `RingQuot (Relation k)` (`UniversalLeavittOver.lean` l.52). Its five relations (l.38–49) are t_0s_0 = 1, t_0s_1 = 0, t_1s_0 = 0, t_1s_1 = 1 and s_0t_0 + s_1t_1 = 1. This is exactly L_{F_2}(1,2) as used here, so the route's item 4 check is done.

## 7. Artifact-only items checked in outline (not queued)
- **Corollary A2 (dyadic odometer factor, entropy 0).**
  - The tower matrix units u^ae_{V_n}u^{−b} give R_X ≅ M_{2^n}(R_n).
  - (V_n, T^{2^n}) is an aperiodic subshift of entropy 0, which embeds in {0,1}^Z (Krieger 1982, recalled). So R_n is generated by 3 elements.
  - The constants of Theorem B depend only on |Σ_n| = 3.
- **Corollary A3** is §6.

## 8. Novelty
- I agree with the lane's firewall. Do not write "first simple Kazhdan group of non-uniform exponential growth" until simple quotients of Sauer–Schesler's acylindrically hyperbolic Kazhdan group are ruled out.
- The defensible statement: explicit infinite, finitely generated, simple Kazhdan LEF groups of non-uniform exponential growth (G_X for Thue–Morse and period doubling), and the elementary-group engine.
