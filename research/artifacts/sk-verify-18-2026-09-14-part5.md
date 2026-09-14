# sk-verify-18 part 5: Theorem Q′ and the finite-action class norm (2026-09-14)

Queue lines:
- **3:** sk-sturmian-growth, `dyadic-tower-subshift-full-group-non-uniform-growth`;
- **4:** sk-deligne-sofic, `finite-actions-with-vanishing-class-norm-make-extension-sofic`;
- **5:** sk-deligne-sofic, `stable-finite-actions-extension-sofic-iff-class-norm-vanishes`.

None carried a sk-verify-19 review line at the time of review.

## Verdicts
- **Line 3, Theorem Q′:** PASS, conditional only on the imports its route requires.
- **Line 4, Theorem 1 (vanishing class norm ⇒ sofic):** PASS, re-derived by hand. It needs no import; the Alekseev–Thom amplification is re-derived below.
- **Line 5, Theorem 2 (stable base: sofic ⇔ vanishing class norm):** PASS-WITH-FIXES. Required fix F1: the Gohla–Thom norm lemmas are printed for groups of finite type, and route step 4 names a model that need not exist for a finitely presented Γ. The half that is needed is re-derived below on the presentation complex.

## Line 3: Theorem Q′ (every use of (V,S) ≅ (X,T) replaced)
Read against the reviewed dyadic proof: sk-cornulier-q7 part 1 §§1–4 and part 2 §§6–7 (PASS by sk-verify-16 and sk-verify-17). The self-conjugacy (M1) enters in exactly five places:
1. **Part 1 §2, tower model:** levels Y_n = X_n × {1,…,8}, T(v,y), L_π, s_y and partial level permutations use only X = ⊔_{i<2^m}T^iV with T^{2^m}V = V, which is (H1).
2. **Part 1 l.50, letter cylinders:** U_a = ζ^m({x_0 = a}), whose S-translates generate the clopen algebra of V "because (V,S) ≅ (X,T) is a subshift". This is exactly (H2), with 𝒫_m in place of {U_a}.
3. **Type-4 generators and A_x:** the ζ_a over the disjoint U_a on sheets (3,4,5), generating (Z/3)^{|A|}. With a partition 𝒫_m they still commute, and A_x ≅ (Z/3)^{|𝒫_m|} × Z. Also ζ_V = ∏_a ζ_a, which Step 2(b) uses for complements.
4. **Counting (part 2 §6):** P_4(ℓ) ≤ (3^{|A|}(2ℓ+1))^{Cℓ^α}·exp(Cℓ^α), with constants depending only on |A|. Replacing |A| by K keeps C and β uniform over the good scales.
5. **Conclusion:** ω ≤ exp(C⌊r_n/3⌋^{β−1}) along scales n → ∞. Only infinitely many good scales are needed, since ω is an infimum. Exponential growth comes from (M3), Matui through Cornulier l.780, for an infinite minimal subshift, which is not an odometer.

**Steps checked to use only (H1):**
- Step 2(c) (twisted 3-cycles through σ_{i,d}^p);
- Step 3: splitting a good U into level pieces W_y, twists in {0,±1} since N = 2^m ≥ 32, and moving three levels into F by Alt(Y_n);
- the (SS) inputs, which are properties of Grigorchuk levels and independent of X.

**Scale bookkeeping:** m = n+3 with n ≥ 5, and the good m range over an infinite set, so large n occur.

**Firewall re-checked:** (H1) at scale m makes f = Σ_j e^{2πij/2^m}1_{T^jV} a continuous eigenfunction with eigenvalue e^{2πi/2^m}. So totally minimal subshifts, Sturmian ones in particular, fail (H1), as stated.

**Imports:** the ones the route names are all reviewed on main: `derived-full-group-generated-by-good-three-cycles`, `minimal-subshift-derived-full-group-exponential-growth`, and `sauer-schesler-grigorchuk-level-estimates` (part 1 of this artifact series).

## Line 4: Theorem 1 re-derived
**Setup.** Γ = ⟨S | R⟩ is finitely presented and residually finite, A is finite abelian, and α classifies 1 → A → Γ̃ → Γ → 1.
- With lifts of S, Γ̃ = ⟨S ∪ A | relations of A, [a,s], r = a_r⟩.
- Proof of the presentation: every relation of Γ̃ maps to a product of conjugates of relators of Γ, which lifts to the corresponding product of central values a_r.

**Amplification.** Given X_n and cochains b_n with defect ν_n → 0, take a chain N_n ⊴ Γ of finite index with ⋂N_n = 1 (Γ is finitely generated and residually finite), put V_n = X_n × Γ/N_n, and pull back b_n.
- Defective cells (v,r) correspond to defective cells (x,r), so the normalized defect is unchanged.
- For g ∉ N_n, g moves every coset, hence every point of V_n. This is the content of Alekseev–Thom Lemma 3.2, used only as credit.

**Torsor permutations.** τ(s)(v,t) = (s·v, t + b(s, s·v)) and τ(a)(v,t) = (v, t+a).
- The A-relations and [a,s] hold exactly.
- The base action is an exact Γ-action, so r returns every v to v, and τ(r a_r^{−1}) fixes (v,t) iff the cell (v,r) is not defective. The fraction of moved points is at most |R|·ν_n → 0.

**Words.**
- A word w trivial in Γ̃ can be written as w′a with w′ ∈ F(S) trivial in Γ and a ∈ A, where the value of w′ in Γ̃ is a^{−1}.
- A van Kampen diagram for w′ has finitely many cells, depending only on w. It maps into the action complex at each base point v, and the A-holonomy of w′ at v is the sum of the cell holonomies. At a base point with no defective cell within radius C_w this is the value of w′, so w fixes (v,t).
- The bad fraction is at most |B_{C_w}|·|R|·ν_n → 0.
- For g ≠ 1 in Γ̃:
  - if g maps nontrivially to Γ, it moves every point for large n;
  - if g lies in A, write it as a word w′a with w′ trivial in Γ; at good base points it acts by translation by g ≠ 0.
  - Either way the moved fraction tends to 1.
- So τ_n is a sofic approximation of Γ̃.

**Model tests re-checked.**
- A split extension has b = 0 and no defect.
- If ν_X = 0 for some finite X, the exact torsor action separates A, and together with residual finiteness of Γ this makes Γ̃ residually finite. So for a non-residually-finite Γ̃, ν_X > 0 for every X, and only the infimum can vanish.

## Line 5: Theorem 2
**⇐:** Theorem 1.

**⇒, checked against Gohla–Thom arXiv:2403.09582v2 (`main.tex` on MSI, read 2026-09-14):**
- `thm:equalzero` (l.373–384), verbatim: "Let Γ̃ be a central extension of Γ by the finite abelian group A and let α … classify this extension. Let (Q,μ) be an A-free measured Γ̃-Boolean algebra and let P := Q^A … Then 0 = θ^P_*(α) ∈ H²(Γ, P(A))." This matches import item 2, with no finiteness hypothesis.
- The unlabeled lemma before `lem:inv` and `lem:inv` itself (l.361–371): a sofic approximation of Γ̃ with finite normal A is equivalent to one on m_n × A with A acting regularly, and the induced limit Γ-action is P_𝒰 = Q^A. This justifies route step 2: P is the limit action of a sofic approximation of Γ. Q is A-free because nontrivial elements of A have ℓ → 1.
- `def:stable` (l.405–407) matches Definition 3.7 as cited: the limit action of any sofic approximation is weakly contained in finite actions.
- `lem:limit` and `cor:weakcont` (l.271–312): the isometric injection of reduced cohomology into ultraproducts, and the contractivity of H^i(Γ,P(A)) → H^i(Γ,P_𝒰(A)), give |||θ^P(α)||| ≥ lim_𝒰 |||θ^{P_j}(α)|||. This matches import item 1 as the proof of `cor:weakcont`. Both are printed for "Γ of finite type" with "BΓ a finite model" (§`sec:coho`, l.121–128).

**F1 (required, 0–2 lines): hypothesis fidelity for finitely presented Γ.**
- The problem: Theorem 2 assumes Γ finitely presented, which is weaker than finite type. Route step 4's "finite model with the presentation complex as 2-skeleton" need not exist.
- **Fix, re-derived.** Work on the finite presentation complex Y (one vertex, S edges, R 2-cells) and define |||c|||_Y = inf_b ‖c − δb‖ on C²(Y,P(A)) with uniform weights on R.
  1. **Restriction.** Classifying Y → BΓ restricts H²(Γ,P(A)) → H²(Y,P(A)), so θ^P_*(α) = 0 gives 0 in H²(Y,P(A)).
  2. **Contractivity.** A measure-preserving inclusion P ⊆ P_𝒰 preserves lengths of cochains on finitely many cells.
  3. **Ultraproduct step.** Given a representative α − δζ of the image in C²(Y,P_𝒰(A)) with small length, write ζ = [ζ_j], which is valid since Y has finitely many cells. Then α − δζ_j represent the X_j-classes with lim_𝒰 of lengths equal. This is GT's proof of the injection half, which never uses 3-cells or expansion.
  4. **Comparison on finite actions.** For finite X, C¹(Y,A^X) = functions S×X → A and δb(r)(x) is the holonomy of b along r at x. So ‖α − δb‖ is exactly the uniformly weighted fraction of defective cells, and |||θ^X(α)|||_Y = ν_X(α) with equality, not only comparability.
- **Replacement for route step 4:** "Norms are taken on the finite presentation complex Y. The inequality of `cor:weakcont` holds there by the same proof, which uses only 1- and 2-cells. On a finite action X, |||θ^X(α)|||_Y equals ν_X(α)."
- **Scope:** if Γ is of finite type, as in GT's printed setting, nothing changes.
- With F1 the chain closes: sofic Γ̃ ⇒ θ^P(α) = 0 ⇒ by stability P ⊆ P_𝒰 of finite actions ⇒ lim_𝒰 ν_{X_j}(α) ≤ |||θ^P(α)|||_Y = 0 ⇒ inf_X ν_X(α) = 0.

**Consequence re-checked.** Over a stable base, a non-residually-finite Γ̃ is sofic, or its class has a uniform positive finite-action lower bound. GT Theorem 3.13 (`thm:main`, l.476–488) is the second case, forced by the cosystolic inequality through `thm:neqzero`. That is consistent.
