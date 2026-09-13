# SK review 3, part 1: the un-* results a generalized note would rely on

Lane `sk-verify-3`, 2026-09-13. Main read at tip `a19fd73b8e`.
This is an independent second concurrence. Every step below was re-derived from the node and artifact text before I read the earlier verdicts.
Verdicts: PASS / GAP (with repair) / FAIL.

## Summary

| claim | verdict | binding caveat |
|---|---|---|
| `steinberg-elementary-groups-are-simple-mod-centre` | PASS | column extraction rests on the Lean kernel check (statement checked at source) |
| `lef-el-groups-force-exactly-matricial-simple-ring`, with `lef-elementary-groups-force-lef-rings` and `simple-lef-rings-are-exactly-matricial` | PASS | rank 3 alone not covered; Krstić–McCool primary still unread (EJZ quote verbatim) |
| `rf-toeplitz-subshifts-over-residually-finite-groups` (Theorem T), with `rf-subshifts-are-periodic-window-approximable` (⇐ direction) | PASS | none |
| `residually-finite-actions-give-matricial-crossed-products` | PASS | injectivity comes from simplicity, so the finite models need not be free |
| `residually-finite-group-toeplitz-elementary-groups-lef-kazhdan` (Corollary T) | PASS | for non-prime q, add a primitive element of F_q to the ring generators (already noted on the node) |
| `subshift-crossed-product-k0-is-coinvariant-group` | PASS (group level) | the order on K_0 is not claimed; rigidity lanes need the positive cone |

No FAIL and no GAP.

## 1. Steinberg simplicity: `steinberg-elementary-groups-are-simple-mod-centre`

Route `-proof`: five requires, all checked.

1. **Ring simplicity** (`steinberg-algebra-simple-iff-minimal-effective`). An import of Steinberg arXiv:1408.6014 Cor 3.6 and Clark–Edie-Michell Cor 4.6, both quoted verbatim on the node. Scope is Hausdorff ample over a field, which matches the claim's hypotheses. PASS.
2. **Local annihilation** (`steinberg-algebras-have-local-annihilation`). Re-derived:
   - Cover supp F by compact open bisections B_j with partial homeomorphisms α_j.
   - For a unit x, P_x = {x} ∪ {α_j(x)} is finite. An infinite unit space gives y ∉ P_x and a clopen W ∋ y missing P_x.
   - Choose V_x ∋ x clopen, disjoint from W, and with α_j(V_x ∩ s(B_j)) ∩ W = ∅. This uses continuity of α_j on the clopen s(B_j); for x ∉ s(B_j), take V_x inside the complement.
   - For clopen V ⊆ V_x and any a: t = χ_W ≠ 0 and s = χ_V a give ts = 0. Also t f s = (χ_W f χ_V) a = 0, since arrows of K with source in V have range outside W.
   - A clopen partition subordinate to the V_{x_i} gives a = Σ χ_{V_i} a, with each term in S_F.
   - Minimality, effectiveness and Hausdorffness are not used, as the node says. PASS.
3. **The criterion** (`local-annihilation-makes-projective-el-simple`).
   - **Source check** (`GroupApproximation/Pestov91/SimpleModCentre.lean` on main):
     - `def LocalAnnihilation` (l.43–45) is `∀ F : Finset R, NonUnitalSubring.closure {s | ∃ t, t ≠ 0 ∧ t*s = 0 ∧ ∀ f ∈ F, t*f*s = 0} = ⊤`. This is the node's S_F verbatim.
     - The theorem (l.327–329) is `isSimpleGroup_elementaryGroup_quotient_center (hcard : 3 ≤ Fintype.card ι) [IsSimpleRing R] (hloc : LocalAnnihilation R) : IsSimpleGroup (↥(elementaryGroup ι R) ⧸ Subgroup.center ↥(elementaryGroup ι R))`.
     - The module is root-imported (`GroupApproximation.lean` l.4897).
     - The module has no `sorry` or `axiom` token. The only grep hit, l.138, is the word "admit" in a docstring.
   - **Not re-audited:** the transitive axiom closure (no builds in this campaign).
   - **Paper steps re-derived:**
     - (a) The coefficients whose roots commute with g form a non-unital subring, so some s ∈ S_F (F = entries of g) gives h = e_ij(s) not commuting with g.
     - (b) ρ − 1 = (g sE_ij g⁻¹ − sE_ij)h⁻¹ has every entry left-annihilated by t, using ts = 0 and t g_pk s = 0.
     - (c) If a c t = 0 for all c, then R a R t = 0, so R t = 0, a contradiction. So some c has (ρ−1)_{qm} c t ≠ 0.
     - (d) From tρ = t we get tρ⁻¹ = t. Then [ρ, e_ml(ct)] = I + (column m of ρ−1)·ct·e_l^T, a one-column matrix in N with a nonzero entry.
     - (e) If (σ⁻¹ − I)_{ll} ≠ 0 for σ = I + w e_l^T, then [σ, e_kl(1)] = e_kl((σ⁻¹−I)_{ll}) is a nonzero root.
   - The remaining case of column extraction (w_l = 0) I did not finish on paper. It rests on the kernel-checked Lean proof.
   - The level-ideal step and the centre clause are re-derived. PASS.
4. **Centre** (`minimal-effective-steinberg-algebras-have-scalar-centre`). Re-derived:
   - χ_{U^c} z χ_U = 0 puts supp z inside the isotropy.
   - supp z is open, so it lies in the interior of the isotropy, which is 𝒢⁽⁰⁾ by effectiveness.
   - Commuting with bisection indicators makes z orbit-invariant, so dense orbits make it constant.
   - Clark–Edie-Michell `thm:center`(1) is quoted. PASS.
5. **(T)** (`elementary-groups-over-fg-rings-have-property-t`). EJZ `thm:main` is quoted verbatim ("finitely generated (associative) ring with 1 and n ≥ 3 ... EL_n(R)"). PASS.

Assembly:
- "Central or everything" is the Lean lemma `normal_le_center_or_eq_top`. It also follows from IsSimpleGroup of the quotient plus perfectness of EL_n, n ≥ 3.
- Infiniteness: e_12(a−b) central forces a = b.
- (T) passes to quotients, and (T) groups are f.g.
- PASS.

Display nit: the body still opens "ESTABLISHED (unreviewed)" although two review PASS lines follow.

## 2. LEF converse: `lef-el-groups-force-exactly-matricial-simple-ring`

**Theorem 1** (`lef-elementary-groups-force-lef-rings`), re-derived step by step from artifact `un-lef-converse-2026-09-13-part1.md` §1.
- **Cover.** A = Z⟨x_r : r ∈ W⟩ is finitely presented. St_N(A) is f.p. for N ≥ 4 (EJZ §6.1, verbatim: "By a theorem of Krstić and McCool [Theorem 3], the Steinberg group St_n(R) is finitely presented for any n≥4 and any finitely presented ring R"). S generates by commutators and products.
- **Prefix induction.** ρ(vs) = ψ(θv)ψ(θs) = ψ(θ(vs)) needs θv, θs, θ(vs) ∈ B, which B's construction guarantees. Each relator maps to ψ(1) = 1, so ρ is a homomorphism St_N(A) → Q.
- **Level ideal.** [x_ij(a), x_jk(1)] = x_ik(a) gives K_ij ⊆ K_ik, and [x_ij(1), x_jk(a)] = x_ik(a) gives K_jk ⊆ K_ik.
  - I checked the cycle link by link, with (i,j,k) = (1,2,3), (2,1,3), (2,3,1), (3,2,1), (3,1,2), (1,3,2): K_12 ⊆ K_13 ⊆ K_23 ⊆ K_21 ⊆ K_31 ⊆ K_32 ⊆ K_12.
  - [x_12(a), x_23(b)] = x_13(ab) makes K two-sided.
  - A/K ≅ ρ(x_13(A)) is finite.
- **Window.** c ∈ D lies in K iff ψ(θ(u_c)) = ψ(1) iff π(c) = 0, using injectivity on B. The differences l(r+s) − (l(r)+l(s)) and l(rs) − l(r)l(s) lie in D = L − L, so φ preserves the listed sums and products, and φ(1) = [1]. PASS.

**Theorem 2** (`simple-lef-rings-are-exactly-matricial`).
- Project each finite model onto one simple factor M_d(F_q) of Q_n/J(Q_n).
- Ψ = [ψ_n]_ω is a unital ring homomorphism, so ker Ψ is a proper ideal, and it is 0 by simplicity.
- For uncountable R, use an ultrafilter on the directed set of windows (already noted). PASS.

Corollary (c) ⇒ (d) is `exactly-matricial-rings-have-lef-general-linear-groups`; over finite fields it needs no Malcev. PASS.

Scope caveat for sk-general-actions-b: the method needs N ≥ 4. St_3(A) is not f.p. when A maps onto F[t] (EJZ, citing KM Cor 2), so rank 3 alone is not covered.

## 3. RF Toeplitz theorem and Corollary T

**Proposition S, ⇐** (`rf-subshifts-are-periodic-window-approximable-proof`).
- With W = B ∪ F⁻¹B and ζ(c)|_W = c|_W, for s ∈ F and b ∈ B we get (s·ζ(c))(b) = c(s⁻¹b) = (s·c)(b) = ζ(s·c)(b). So the approximation is exact on B.
- Coverage of L_W(X) gives density.
- Perfectness lets ζ be made injective, because pattern cylinders are infinite.
- PASS for the direction used.

**Theorem T** (`rf-toeplitz-subshifts-over-residually-finite-groups`, artifact part 2 §6).
- **Well-defined.** The hole C_m avoids g_1..g_m, so ∩ C_m = ∅. The condition d_m ≥ m+2 leaves room for the hole plus a 1-subcoset.
- **Minimal.** For finite W, pick M with W ∩ C_M = ∅. Normality gives γw ∈ Γ_M w, so the return set contains Γ_M, which is syndetic.
- **Free.**
  - g·x = x transports x on Γ_m-cosets.
  - C_m is the unique non-constant Γ_m-coset: F1 makes every skeleton coset constant, and F2 makes C_m non-constant.
  - So g⁻¹C_m = C_m, hence g ∈ Γ_m for every m, and g = e.
  - A dense free orbit gives topological freeness: an open V ⊆ Fix(g) contains some γx, so γ⁻¹gγ = e.
- **RF.**
  - The map γ̄ ↦ Γ_{M+1}γgw is injective (γγ'⁻¹ ∈ Γ_{M+1}) between sets of size d_{M+1}, so it is a bijection.
  - Each hole position has two bad classes, so at most 2|W| ≤ 2|B_M| < d_{M+1} classes are bad.
  - For a good γ, skeleton positions keep their values (F1) and hole positions read 0.
  - So every W-window of p_M is a window of x, and the orbit of p_M covers L_W.
- PASS.

**Matricial crossed product** (`residually-finite-actions-give-matricial-crossed-products`, artifact un-measure part 1 §2).
- **Simplicity.** A free point in the open set {f_e = c}: the finitely many Fix(g) are closed with empty interior. Then a clopen W with gW ∩ W = ∅ gives χ_W P χ_W = cχ_W, and minimality gives 1 ∈ J.
- **Windows.** P(g)D(f′)P(g)⁻¹ = diag f′(ζ(β(g⁻¹)z)) and D(f′∘α(g)⁻¹) = diag f′(g⁻¹ζ(z)) agree when f′ is ε-locally constant and g⁻¹ ∈ F. Also P(g)P(h) = P(gh), because β is a genuine action.
- **Injectivity** comes from simplicity through the unital ultraproduct homomorphism. So I withdraw my own initial worry: the models need no freeness at scale, and collisions of matrix entries do not matter.
- PASS.

**Corollary T** (`rf-group-toeplitz-elementary-groups-lef-kazhdan-proof`).
- **Generation.** u_g 1_U u_g⁻¹ = 1_{gU} = 1_{[x(g)=1]}.
- **Steinberg hypotheses.** The transformation groupoid is Hausdorff, ample, minimal, effective (it is topologically free) and has a compact infinite unit space.
- **LEF of the quotient.**
  - The scalar is ω-almost constant, because F_q^× is finite. With injectivity this puts the kernel of EL_N → ∏_ω (GL/F_q^×) at the scalars.
  - ∏_ω GL/∏_ω F_q^× = ∏_ω (GL/F_q^×), since the ultraproduct of a constant finite group is itself.
- PASS.

## 4. K_0: `subshift-crossed-product-k0-is-coinvariant-group`

- **Step 2.** A[t_1..t_p] is a filtered colimit of Noetherian regular rings with flat transition maps. So it is coherent: kernels are computed at a finite stage and stay f.p. after flat base change. It is also regular: resolutions transport.
- **Hypotheses.** ABC Lemma 7.2 needs regular supercoherent, and Theorem 3.6 needs unital R with A = Z, H-unital. Both are quoted verbatim.
- **Negative K-theory.** K_{−1}(F_q^P) = 0 (Bass, recalled), and K-theory commutes with filtered colimits (quoted), so K_{−1}(A) = 0.
- **Identification.** σ(χ_U) = χ_{TU} = T_*χ_U, so the cokernel is C(X,Z)/(1−T_*).
- **Model test.** T = id agrees with the fundamental theorem.
- PASS at group level.

Caveat for sk-rigidity-*: this computes only the abelian group and the class of 1. It does not give the positive cone. G_X ≅ G_Y reaches K_0 only through a ring (anti-)isomorphism, which is itself open in characteristic 2.

## 5. What these give a generalized note (calibration for sk-general-actions-*, sk-universal-embedding-*, sk-rigidity-*)

Twice-reviewed chain. Let Γ be f.g., X ⊆ A^Γ a minimal topologically free subshift that is residually finite in the Kerr–Nowak sense, and q a prime power. Then EL_N(LC(X,F_q) ⋊ Γ)/Z is infinite, f.g., simple, Kazhdan and LEF for N ≥ 3, and Theorem T supplies such an X for every f.g. infinite RF Γ.
- **Universal embedding.** The only step Corollary T does not already contain is γ ↦ diag(u_γ, u_γ⁻¹, 1) ∈ EL_3 (Whitehead). This map is injective modulo the centre, because diag(u_γ, u_γ⁻¹, 1) = λI forces γ = e. That lemma is sk-universal-embedding-a's to land and review.
- **The note's own Z-proof** (l.154–227) uses none of these nodes. Replacing it by the Steinberg criterion would swap a self-contained page for a citation to a Lean-certified, unpublished criterion credited to Stepanov's Lemma 4.3. That is a reader trade-off for the proof lanes to weigh, not a correctness issue.
- **Not independently read by me:** the Krstić–McCool primary; the Kerr–Nowak Definition 2.1 primary (read by un-verify-measure); ABC's own proof of Theorem 3.6.
