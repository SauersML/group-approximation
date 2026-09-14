# SK review 5, part 3: Cartan reduction and ring invariants, the unitary gap firewall, unique trace, thin cylinders (2026-09-13)

Lane sk-verify-5. This covers queue priorities 4b, 5 and 6 of `sk/queue/sk-verify-5.txt`; every step was re-derived by hand at main 0aeefbbba1. Verdict key as in part 1. Nothing here touches the note's proof.

## 0. Verdicts

| # | claim | owner | verdict |
|---|---|---|---|
| 17 | `subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity` (Theorem C) | sk-rigidity-cartan | PASS |
| 18 | `subshift-ring-isomorphism-preserves-soe-class-and-growth` (Theorem G) | sk-rigidity-cartan | PASS |
| 19 | imports: ACCCLMRSS reconstruction, Steinberg 2019 Cor `c:effective.case.gpd.rec`, Nekrashevych `pr:shiftgrowth` | sk-rigidity-cartan | use-consistency PASS; primary sources not re-read, and no nodes edited |
| 20 | `fp-simple-groups-have-no-gapped-finite-unitary-models` (Theorem U) | sk-fp-sofic-c | PASS |
| 21 | `lst-quasisimple-classical-character-ratio-bound` | sk-fp-sofic-c | PASS as import; the support-≥-1 lemma PASS |
| 22 | `fp-simple-groups-have-no-classical-group-unitary-models` (Corollary C) | sk-fp-sofic-c | PASS |
| 23 | `subshift-elementary-group-reduced-cstar-has-unique-trace` | sk-strong-2 | PASS |
| 24 | `thin-cylinder-sft-tiling-families-force-periodic-points` (+ Corollaries 1–4) | sk-labbe-matricial | PASS |

The open targets stay OPEN:
- Cartan uniqueness (`subshift-crossed-product-algebraic-cartans-are-conjugate`);
- a finitely presented infinite simple sofic or hyperlinear group;
- row 7, exact matriciality of Labbé's crossed product.

## 1. Theorem C (Cartan uniqueness ⟺ groupoid-model rigidity)

**§1, twists over F_2 are trivial.**
- T = {1}. (DT1) gives q^{-1}(G^(0)) = Σ^(0). So q(σ) = q(τ) forces s(σ) = s(τ) and στ^{-1} ∈ Σ^(0), hence σ = τ.
- (DT2) gives local continuous inverses.
- Contravariance under R^× = {1} is vacuous, so A_{F_2}(G;Σ) = A_{F_2}(G) with diagonal onto diagonal.

**C.1.** 𝒢_X is free, so principal, so effective. `prop:effectiveACPprincipalADP` applies with R = F_2, which is indecomposable.

**C.2, the model groupoid G_B.** The chain lem:C=>Q → thm:main → prop:Hausdorff → prop:effective(a) → §1 gives the model.
- **Compact unit space.** A maximal commutative B contains Z(R_X) ∋ 1, and the Stone space of I(B) is compact; R_X is countable, so it is metrizable.
- **Minimal.**
  - For open invariant U, I_U = span{1_S : s(S) ⊆ U} is closed under left multiplication because s(TS) ⊆ s(S).
  - It is closed under right multiplication because s(ST) lies in the orbit of s(S), and U is invariant.
  - At a unit x, 1_S(x) ≠ 0 forces x ∈ S, so x = s(x) ∈ U. Elements of I_U therefore vanish at units off U, and 1 ∉ I_U. This contradicts simplicity.
- **No isolated points.**
  - If x is isolated, G^x_x = r^{-1}(x) ∩ s^{-1}(x) is open, hence trivial by effectiveness. Then e = 1_{{x}} has eR_Xe = F_2e.
  - So eR_X is a minimal right ideal, and the socle is a nonzero ideal, hence R_X.
  - A unital ring equal to its socle is semisimple Artinian, so R_X = M_n(F_2) is finite. Contradiction.

**C.3.**
- **(b) ⇒ (a).** Composing Φ with the diagonal-preserving Ψ induced by 𝒢_X ≅ G_B gives β = Φ^{-1}Ψ with β(D_X) = B.
- **(a) ⇒ (b).** A ring isomorphism between F_2-algebras is F_2-linear.
  - Every clause of `def:ACP` (local units, span of idempotents, span of the normaliser, faithful conditional expectation, maximal commutativity) is ring-theoretic or F_2-linear, so it transports along Φ.
  - (a) gives β. Then Φ^{-1}β is diagonal-preserving A(𝒢_X) → A(G), and Steinberg's corollary, with the domain 𝒢_X effective, gives G ≅ 𝒢_X.

**C.4.** 𝒢_Y ≅ 𝒢_X maps full compact open bisections to full compact open bisections.
- 𝒢 is principal, so a full bisection is determined by its homeomorphism, and [[𝒢_X]] = [[T]].
- The GPS / Bezuglyi–Medynets import (PASS in sk-review-3 part 3 and sk-review-5 part 1) gives flip conjugacy.

**C.5.** EL_3(β) maps L_Y onto GL_3(β(D_Y)) = GL_3(B). Theorem A (PASS twice) applies to EL_3(β)^{-1}α.

**§4, inner conjugate check.**
- w = 1 + e_U u with U ∩ TU = ∅ satisfies w² = 1.
- I computed w e_V w = e_V + (e_{U∩TV} + e_{U∩V})u, since the u² term lies over U ∩ TU = ∅.
- For V = U this is e_U + e_U u ∉ D_X. The artifact displays a vanishing u² term in a different form; the conclusion is the same.

## 2. Theorem G (a ring isomorphism preserves the SOE class and complexity growth)
- **SOE.** Theorem R with m = 1 (PASS twice).
- **Growth.**
  - 1 ∈ V_X and ⋃V_X^k = R_X, so the finite-dimensional Φ(V_Y) lies in V_X^C, and Φ(V_Y^n) ⊆ V_X^{Cn}.
  - Nekrashevych's two-sided estimate gives ⌊n/2⌋p_Y(⌊n/2⌋) ≤ (2Cn+1)p_X(2Cn), and symmetrically.
- **Entropy.** With n = 2m, m p_Y(m) ≤ (4Cm+1)p_X(4Cm). Take logs, divide by m, and use h = lim (1/n) log p(n): h(Y) ≤ 4C h(X).
- **GK dimension.**
  - p is nondecreasing, since right extensions give L_{n+1} ↠ L_n. So the limsup of log p(m)/log m over even m equals the limsup over all m.
  - The upper and lower estimates give GKdim R_X = 1 + limsup log p_X(n)/log n.
  - GK dimension is independent of the generating subspace, so the exponents agree.
- **Scope.** The Boyle–Handelman caveat is stated correctly: no claim is made that ring isomorphism is finer than SOE for subshifts.

**Imports (item 19).**
- The statements used match the verbatim quotes in the three `-citation` routes:
  - ACCCLMRSS l.615–628 `def:ACP`, `lem:C=>Q`, `thm:main`, `prop:Hausdorff`, `prop:effective`, `prop:effectiveACPprincipalADP`;
  - Steinberg `c:effective.case.gpd.rec`, which puts effectiveness on the domain groupoid only;
  - Nekrashevych `pr:shiftgrowth`, including the cross-product identification.
- I did not re-read the primary sources, and I added no review line to the import nodes.

## 3. The unitary gap firewall

**Theorem U.**
- **Step 0.** Π is a homomorphism into the tracial ultraproduct, and ‖AB − A′B′‖_2 ≤ ‖A−A′‖_2 + ‖B−B′‖_2 for unitaries. So ρ_k(W_k(w)) and π_k(w̄) agree in the limit. Injectivity gives η_g > 0 for g ≠ e.
- **Step 1.** ρ(q) − I vanishes on the trivial isotypic part and has norm ≤ 2 elsewhere, so ‖ρ(q) − I‖_2² ≤ 4(1 − w^0). Hence lim_ω(1 − w^0_k) ≥ η_c²/4.
- **Step 2.** Re τ(ρ(q)) = w^0 + Σ_{χ≠1}(m_χχ(1)/d)Re(χ(q)/χ(1)) ≤ w^0 + (1−w^0)θ at noncentral q, so ‖ρ(q) − I‖_2² ≥ 2(1−θ)(1−w^0). With 1 − w^0_k ≥ η_c²/8 for ω-almost all k, this gives δ = (1−θ)η_c²/4.
- **Step 3.** The finitely many relators satisfy ‖ρ_k(W_k(r)) − I‖_2 → 0, so W_k(r) ∈ Z(Q_k) for ω-almost all k.
- **Step 4.** x ↦ φ_k(x)Z kills R, giving ψ_k: S → Q_k/Z. Its kernel is S, since S is infinite simple and Q_k is finite, so φ_k(X) ⊆ Z(Q_k).
- **Step 5.** Then W_k([x,y]) = 1, so η_c = 0. Contradiction.
- **Model tests.**
  - SL_3(Z) is not simple, so Step 4 fails there.
  - G_X is not finitely presented, so Step 3 has no finite relator set.
  - Linear characters of GL_N(q) at noncentral elements have ratio 1. So GL_N itself is not gapped, which is why Corollary C passes to commutator subgroups.

**LST import.** Theorem 1.2.1 and Definition 4.1.1 are quoted verbatim from Ann. of Math. 174 (2011), pp. 1889 and 1907; I did not re-read them.
- **The support lemma.** supp(g) = 0 means ρ(g) is scalar over F̄.
  - The kernel of the natural representation of a quasi-simple classical group is central (e.g. Spin → SO), so [g,h] ∈ ker ρ ⊆ Z(Γ) for every h.
  - Then gZ is central in the simple nonabelian Γ/Z(Γ), so g ∈ Z(Γ).
  - With N = 1, q^{-1/481} ≤ 2^{-1/481}.

**Corollary C.**
- Infinite simple S is perfect, so a finite set X′ of commutators of words generates S, and S is finitely presented on X′.
- For x′ = [a,b], put φ′_k(x′) = [W_k(a), W_k(b)] ∈ [Q_k,Q_k]. The induced homomorphism is the same Π, because Step 0 uses the maps only through products on generators.
- [Q_k,Q_k] is quasi-simple classical, hence θ-gapped by LST. Theorem U applies with target [Q_k,Q_k] and its own centre.
- Sofic approximations through actions are the permutation-representation case: normalized fixed points are normalized traces.

## 4. Unique trace
- Over F_2 the centre is trivial, so G is simple.
- G is infinite with (T) (PASS in part 1 §1), so G is nonamenable.
- The amenable radical is a normal amenable subgroup, hence {e}.
- BKKO Theorem 4.1, on main as `bkko-reduced-traces-concentrate-on-amenable-radical` (verbatim import), gives τ(λ_s) = 0 for s ≠ e.
- Over F_q, apply the same argument to G/Z.
- Unique trace does not decide C*-simplicity (Le Boudec), and the node says so.

## 5. Thin cylinders (sk-labbe-matricial)
**Axioms checked on main.** (Q1) of `sft-crossed-product-fp-iff-quantum-rigid` requires ORTHOGONAL idempotents. The proof needs this: in characteristic 2, commuting idempotents summing to 1 need not be orthogonal (three copies of 1).
- **(⇐).** Put E_a(z) = [x(z) = a] for a (0,L)-periodic point.
- **Step 1.** Periodicity moves a site to a representative at vertical distance ≤ ⌊L/2⌋ ≤ 2D, because L ≤ 4D+1. So any two sites in columns within 2D commute by (Q2), and within one column everything commutes. E_β(c) is idempotent, the E_β(c) are orthogonal for distinct β by (Q1), and Σ_β E_β(c) = Π_j Σ_a E_a(c,j) = 1.
- **Step 2.** In an illegal window the factors commute. The (Q3) product at (c+D, j) consists of factors already present, with repeated residues collapsing by idempotence when 2D+1 > L. So the window product is 0.
- **Step 3.** Legality is local and B is finite. By König, if no W_0 existed there would be a bi-infinite legal word, and x(c,j) = β_c(j mod L) would lie in Ω (all B_D-patterns legal, D ≥ r) with period (0,L).
- **Step 4.** The noncommutative distributive expansion of Π_c Σ_β E_β(c), in increasing c, puts every term over an illegal word of length W_0. Such a word contains an illegal window of consecutive factors, since W_0 > 2D automatically, so 1 = 0.

**Corollaries.**
- **Corollary 1.** Freeness excludes periodic points, and (T1)–(T3) give (Q1)–(Q3) for E_a(z) = e_a(z mod Λ).
- **Corollary 2.** U_2^ℓ centralizes the family iff the family is (0,ℓ)-periodic.
- **Corollary 3.** If U_2^ℓ were scalar it would centralize, so the image in PGL_d(F_q) has order ≥ 4D+2, and |PGL_d(F_q)| < q^{d²}.
- **Corollary 4.** r = 1, so the Labbé witness tori are at least 14 × 14 at D = 3.
- **Scope.** Fat tori and diagonal short vectors are correctly excluded from the claim.

## 6. Status for main
- No FAIL and no GAP. The note's nodes are unaffected.
- Imports assumed as recorded: ACCCLMRSS, Steinberg 2019, Nekrashevych 2016, LST 2011, BKKO Theorem 4.1, and GPS / Bezuglyi–Medynets (already PASS).
- The queue `sk/queue/sk-verify-5.txt` is complete through line 23.
