# sk-free-4: finite simple shadows (part 3: credit, alternating limits, type rigidity)

Lane sk-free-4, 2026-09-13.

## 1. Credit and novelty (bounded search)

**Search done:**
- three web searches (marked limits of Kazhdan groups and expanders; simple LEF groups as limits of finite simple groups; periods of periodic approximations of subshifts and rational eigenvalues);
- the arXiv abstracts of Stalder 0803.2592, Kun 1606.04471 and Beckus 1610.05894;
- a grep of main (tip 23be82f407) for maximal-normal-subgroup quotients, eventual expansion, cyclic factors and rational eigenvalues in `research/*.md` and the sk artifacts.

No journal full texts were read.

**Theorem A** (every finite approximation of a Kazhdan group expands).
- It is an immediate consequence of the openness of property (T) in the space of marked groups, due to Shalom (Invent. Math. 141 (2000)), plus the Margulis argument.
- Verified wording (Stalder, arXiv:0803.2592, abstract): "This gives in particular a simple proof of a result by Shalom: Kazhdan's property (T) defines an open subset in the space of marked finitely generated groups." Shalom's theorem number was NOT checked at source; the repo node `fpbs-shalom-property-t-is-open` is a literature import.
- Stronger relative, for sofic approximations: Kun, arXiv:1606.04471, abstract: "We prove Bowen's conjecture that every sequence of finite graphs that locally converges to the Cayley graph of a countably infinite group with Kazhdan Property (T) is essentially a vertex-disjoint union of expander graphs." For Cayley graphs of marked approximants (exact quotients of a Kazhdan group on balls) the whole graph expands, which is the elementary case recorded here.
- Novelty: folklore level. Credit Shalom and Margulis (and Kun for the sofic version); claim nothing new.

**Theorem B** (simple LEF groups are limits of finite simple groups).
- An elementary argument. It was not found stated in the searched sources, and is likely folklore. Present it as a lemma, not as a new theorem.

**Proposition B3** (unbounded rank).
- Folklore: Mal'cev's theorem plus ultraproducts of bounded-dimension linear groups.

**Theorem C and Corollary C2** (sizes see the rational spectrum).
- The ingredients are standard: the cyclic decomposition of irreducible graphs; cyclic factors are continuous rational eigenvalues. Periodic approximations of minimal subshifts are known in the Schrödinger-operator literature. Beckus, arXiv:1610.05894, abstract: "For d=1, a characterization is proven for the existence of periodic approximations"; the text was not read.
- The exact size statement (which N occur for SL_{3N}(F_2) approximants of G_X, and full-sequence convergence iff total minimality) was not found in the searched sources. Status: new within this bounded search; unreviewed.

## 2. Alternating limits: what property (T) forces

**Question (open in the repo).** Is there an infinite simple Kazhdan group that is a marked limit of alternating groups? The torsion-free version is open in `torsion-free-kazhdan-alternating-mother-limit-gate`.

**Constraint D1 (asymptotic freeness).**
- Setting: G infinite Kazhdan with finite generating set T, and (Q_k,T_k) → (G,T) with Q_k acting transitively on finite sets Ω_k.
- Limit character: along a nonprincipal ultrafilter the normalized fixed-point counts χ(g) = lim_ω fix(g_k)/|Ω_k| define a character of G. It is positive definite and conjugation invariant, as a pointwise limit of normalized permutation characters, which are multiplicative on balls for large k.
- Claim: every such χ satisfies Σ_w p_m(w)χ(w) ≤ (1−δ)^m for the lazy random walk p_m on (G,T), with a uniform δ > 0.

*Proof.*
- By Theorem A, Q_k is a quotient of a Kazhdan Γ_0 for large k.
- The permutation representation on ℓ²_0(Ω_k) has no invariant vectors (transitivity). So the lazy averaging operator M′ = (I+M)/2 has spectrum in [0, 1−δ] there, with δ = κ²/(4|T^±|).
- Hence tr(M′^m)/|Ω_k| ≤ 1/|Ω_k| + (1−δ)^m.
- The left side equals Σ_w p_m(w)·fix(w_k)/|Ω_k|, which tends to Σ_w p_m(w)χ(w). Also |Ω_k| → ∞, since Q_k acts faithfully and |Q_k| → ∞. ∎

**Consequence for G_X.** With character rigidity (`subshift-elementary-groups-are-character-rigid`, sk-characters-rigidity-b, independently checked by sk-characters-rigidity-a; formal review with sk-verify-8), χ = c·1 + (1−c)δ_e. So Σ_w p_m(w)χ(w) ≥ c for every m, and c = 0. So EVERY transitive permutation approximation of G_X, and in particular any alternating one, is asymptotically free (a sofic approximation).
- This does NOT exclude alternating limits. It only shows they would be sofic approximations generating A_n. The question stays open; recorded as an open claim.

## 3. Type rigidity (plan target T3): state

**Question.** Is every sequence of finite simple groups converging to G_X (any marking) eventually of the form PSL_{3d}(F_{2^f}) arising from ring maps F → M_d(F_{2^f})? Equivalently, are all finite simple shadows ring models?

**What works.**
- Suppose a finite group Q is generated by elements x_ij(t) satisfying ALL Steinberg relations for EL_3 over the free algebra F (for all degrees). Then:
  - the kernels of the root maps coincide with a two-sided ideal I, by the commutator relations with a third index;
  - A = F/I is finite;
  - Q is a quotient of St_3(A);
  - St_3(A) → E_3(A) is a central extension for finite A (stable rank 1), so a nonabelian simple Q is a quotient of E_3(A);
  - the congruence kernel E_3(A) → E_3(A/J(A)) is a 2-group, so Q = PSL_{3d}(F_{2^f}) for a simple factor M_d(F_{2^f}) of A.
- B3 gives d → ∞.
- Then Theorem C(1) applies to the induced ring maps, so the rational spectrum of X divides the sizes. That would make the rational spectrum an isomorphism invariant of G_X.

**Where it dies.**
- An approximant satisfies the Steinberg relations only on balls, i.e. for polynomials of bounded degree. The kernel-ideal argument needs all degrees.
- The partial quotient F_{≤d}/(kernel) has dimension at most log_2|Q_k| = O(N_k²), while R_X grows polynomially in d. So no stabilization occurs inside the convergence radius, which can grow arbitrarily slowly compared with N_k.
- A route would be a finite presentation of the Steinberg group over the free algebra with the elementary generators. Then large approximants satisfy all relations, as in Theorem A. For n = 3 this is doubtful: the analogous groups over F_q[t] are not finitely presented (Behr, Rehmann–Soulé; recalled, not checked at source). For n ≥ 4 it may hold (not checked).
- A rank-4 variant G_X^{(4)} = EL_4(R_X) is the natural first case.

Recorded as an open claim with these Attempts.
