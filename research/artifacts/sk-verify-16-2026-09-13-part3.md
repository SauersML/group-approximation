# sk-verify-16 part 3: wave-11 queue lines 64–70 (2026-09-13)

Lane sk-verify-16, an independent verifier serving `sk/queue/sk-verify-13.txt` lines 64–70. Parts 1–2: `research/artifacts/sk-verify-16-2026-09-13.md` and `-part2.md`. Every step below was re-derived by hand from main at tip aaa00d6aae, and every citation was checked against the arXiv e-print on MSI.

## 0. Verdicts
| line | claim | verdict |
|---|---|---|
| 64 | `dyadic-substitution-derived-full-groups-non-uniform-growth` | **PASS** (conditional on the named imports, all checked at source or reviewed) |
| 65 | `simple-amenable-group-of-non-uniform-exponential-growth` | **PASS** (conditional on line 64 and Matui/Juschenko–Monod imports) |
| 66 | `derived-full-group-generated-by-good-three-cycles` (import) | **PASS-WITH-FIXES** (quotation display) |
| 67 | `minimal-subshift-derived-full-group-exponential-growth` (import) | **PASS** |
| 68 | `bounded-width-subgroups-of-subshift-gl-are-locally-finite` | **PASS** |
| 69 | `subshift-el3-two-ended-lattice-stabilizers-locally-finite` | **PASS** |
| 70 | `finite-dimensional-combs-generate-popa-algebras` | **PASS** |

No FAIL, no GAP.

## 1. Sources checked at source (MSI, 2026-09-13)
**Cornulier, arXiv:2002.09342 e-print `bou1064.tex` (1220 lines).**
- l.166: Matui's exponential growth for infinite minimal subshifts.
- l.216: question (7), "Le groupe $\lb\vpi\rb'$ a-t-il une croissance exponentielle uniforme?"
- l.576–579: Définition `d_bon`.
- l.580–583: Lemme `eng_cb`, "Soit $(X,\vpi)$ un sous-décalage minimal infini sur $\Z$. Le groupe $\lb\vpi\rb'$ est engendré par les $\sigma_U$, où $U$ parcourt les clouverts bons."
- l.778–780: Théorème `expo` (Matui), for minimal non-odometer systems. An infinite subshift is expansive, so it is not an odometer.

**Sauer–Schesler, arXiv:2605.30163 e-print `nonuniformgrowth.tex` (1429 lines).**
- Spherical transitivity at l.488.
- `lem:separation` at l.615–638, d_{Γ_n}(ρ_n,η_n) ≥ 2^{n−3}.
- The Grigorchuk bound at l.648.
- The Bartholdi–Erschler inverted-orbit bounds at l.682 and l.695 (for ξ_n, k ≤ r_n).
- `lem:commuting-conjugates` at l.920 and `lem:normal-form` at l.969.
- `lem:count-p1..p4` at l.1038–1191 (ℓ ≤ r_n, and ℓ ≤ r_n/3 for P_3).
- The complete bipartite linking graph at l.1392.

These are items (SS1)–(SS5) of the import node `sauer-schesler-grigorchuk-level-estimates`, which has no review line on main. I found its items consistent with the source. The source uses Y_n = X_n × {1,2,3,4} and Sym(4); the lane uses 8 sheets and Alt(8), and the counts transfer with 20160 in place of 24.

## 2. Line 64: Theorem Q
**Tower model.**
- (M1), iterated, gives V_m clopen, X = ⊔_{i<2^m}T^iV_m, and (V_m, T^{2^m}) ≅ (X,T).
- L_π ∈ [[T]]: on V×{y} it is T^{β(πy)−β(y)}. π ↦ L_π is an injective homomorphism, and Alt(Y_n) perfect gives L(Alt) ≤ [[T]]′.
- s_y = T^N on its level.
- σ_{y,y′} = [s_y, L_{(y y′)}]: I computed (v,y) ↦ (Sv,y) and (v,y′) ↦ (S⁻¹v,y′).

**Generation, W_n = [[T]]′.**
- **Step 1.** Fibre conjugation by 𝒢_n (SS5) gives Alt(F_x) for every x. The linking involution conjugates ((x,1) b c) to ((y,1) b c). With Alt(8) 6-transitive this gives every crossing 3-cycle. Overlap ≥ 2 gives Alt(P∪Q), and connectivity (SS4) gives Alt(Y_n).
- **Step 2(b).** 𝔅 is closed under complements, ζ_{V∖B} = ζ_Vζ_B⁻¹. It is closed under intersections: I computed [(1 2 3),(3 4 5)] = (1 4 3) with 1→4→3→1 and 2, 5 fixed, pointwise over B∩B′ and trivial over the symmetric difference. It is closed under S^{±1}, via conjugation by σ_{1,4}σ_{2,5}σ_{3,6}. So 𝔅 is the whole clopen algebra of V, since the letter cylinders generate it as a subshift.
- **Step 2(c).** Twisted 3-cycles: χζ_Bχ⁻¹(S^pv,i) = (S^qv,j).
- **Step 3.** Good U splits into good pieces over levels with disjoint supports. Each σ_W is a twisted 3-cycle on three consecutive levels with twists in {0,±1}. Alt(Y_n) (3-transitive) moves it into F, since L_πs_zL_π⁻¹ = s_{πz}. With Lemme `eng_cb`, W_n = [[T]]′.

**Counting.**
- Lemma 5.1: type 3 against type 4 sit on disjoint sheets. Type 2 against 3/4: a common fibre point would give d(ρ_n,η_n) ≤ 2r_n + 1 < 2^{n−3} for large n.
- Lemma 5.2: the normal form w = g_1⋯g_ℓ ∏_i a_i^{g_i⋯g_ℓ} with type separation, as in S–S `lem:normal-form`.
- P_1 ≤ γ_𝒢(ℓ).
- P_2: one Alt(8) element per point of an inverted orbit.
- P_3: one permutation of an inverted orbit of a word of length ≤ 3ℓ.
- P_4: per point, (Z/3)^{|A|} × Z with the Z-coordinate in [−ℓ,ℓ]. Conjugates at the same point agree, because type 1 acts trivially on sheets and V-labels.
- So γ(ℓ) ≤ exp(Cℓ^β) for ℓ ≤ r_n/3.
- ω(G,T_n) = inf_k γ(k)^{1/k} ≤ exp(C⌊r_n/3⌋^{β−1}) → 1.
- Exponential growth by Matui (l.780).

**Hypotheses.**
- Constant length 2 gives the dyadic towers matching X_n × 8 sheets.
- The subshift property bounds the letter partition, so |T_n| is bounded. The odometer model test fails exactly here, as the lane notes.
- Large n is needed for SS3 and for the parity and transitivity steps.

## 3. Line 65: amenable simple example
- Thue–Morse (0↦01, 1↦10) is primitive of constant length 2 with non-periodic fixed point, so X is an infinite minimal subshift and line 64 applies.
- [[T]]′ is simple and f.g. (Matui), amenable (Juschenko–Monod, via `minimal-cantor-full-groups-are-amenable`), and infinite (it contains a lamplighter).
- Osin's theorem (elementary amenable ⇒ uniform) is correctly used only as a no-conflict remark.
- The novelty claim is correctly bounded.

## 4. Line 66: good 3-cycles generate [[φ]]′ (import): PASS-WITH-FIXES
- Content matches l.576–583.
- **Fix (display):** the node's "verbatim" block renders the source's arrow display `$$U\stackrel{\vpi}\longrightarrow\vpi(U)\stackrel{\vpi^{-2}}\longrightarrow\vpi^{-1}(U)\stackrel{\vpi}\longrightarrow U.$$` as an inline paraphrase "(par φ, φ^{−2}, φ)". Say "verbatim up to the typesetting of the arrow display".
- The source's proof summary (simplicity, special 3-cycles, Matui Lemma 5.1) is accurate.

## 5. Line 67: Matui's exponential growth (import): PASS
- l.166 and l.780 are verbatim.
- The node's hypothesis, infinite minimal subshift, implies the source's "not an odometer".

## 6. Line 68: bounded-width subgroups are locally finite: PASS
- **Faithful banded representation.** π(fu^k)δ_t = f(T^{t+k}y)δ_{t+k}, with the dense orbit of y.
- **Windows.** U_t = span π(Γ)(δ_t ⊗ F_q^m) lies in a window of dimension ≤ m(2p+1). It is Γ-invariant, and ΣU_t = M, so Γ embeds in ∏_t GL(U_t).
- For Δ = ⟨γ_1..γ_k⟩ the kernels N_t ⊴ F_k have index ≤ |GL_{m(2p+1)}(F_q)|, so there are finitely many. Their intersection has finite index, so Δ is finite.
- Model tests (e_12(u); diag(u,u⁻¹,1); SL_3(F_q[u])) are correct.

## 7. Line 69: two-ended lattice stabilizers: PASS
- The action on 𝓛_± is right multiplication. Width w moves u^aO_+³ into u^{a−w}O_+³, and finite generation is preserved via the free quotient of rank 6w.
- **One end.** O_+³g = O_+³ iff g, g⁻¹ ∈ M_3(B[u;α]). It contains SL_3(F_2[u]) = E_3(F_2[u]), which contains SL_2(F_2[u]) (Nagao amalgam, free subgroups).
- **Both ends.** L_+g = L_+ gives degrees ≥ −2n for g and g⁻¹, and L_- gives ≤ 2n. So the width is ≤ 2n, and line 68 applies. The standard pair gives G_X ∩ GL_3(B).

## 8. Line 70: combs give Popa algebras: PASS
- **Step 1.** ρ_j(x) = e_jxe_j is a unital *-homomorphism on A_i (j ≥ i), since e_j commutes with A_j ⊇ A_i. By (C2) the direct sum is injective, so A_i is RFD, hence QD. Quasidiagonality passes to the norm closure of the increasing union by the local (Voiculescu) characterization and Arveson extension.
- **Step 2.** With e = e_i and B = e_iA_ie_i: ‖[x,e]‖ ≤ 2‖x−x′‖, and ex′e ∈ B. B ≠ 0 by (C3).
- **Step 3.** A nonzero ideal J meets some A_i, since otherwise the quotient map is isometric on the dense union. Then (C2) gives e_jxe_j ≠ 0 in K = J ∩ e_jA_je_j, which is an ideal of the simple D. So e_j ∈ J, and by (C3) 1 ∈ J.
- The corner-trace consequence is the η = 0 case of line 59's bound, with y_s ∈ A_j.
- The UHF, T1 and C⊕C model tests are correct.

## 9. Not checked
- Primary papers not opened: Bartholdi–Erschler (Invent. Math. 189 (2012)), Matui's lamplighter paper, Mossé 1996, Nagao.
- The journal version of Sauer–Schesler.
- The Connes–Jones property (T) definition used in sk-popa-lgx part1 §2 (mechanism G, not in these queue lines).
- Novelty beyond the lanes' own bounded searches.
