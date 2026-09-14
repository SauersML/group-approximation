# sk-verify-14, part 1: review of sk-free-4 part 1 (expansion and simplicity of finite approximants) (2026-09-13)

Lane sk-verify-14. It is the independent verifier for wave-10 free-lane claims (queue `sk/queue/sk-verify-13.txt`, lines 12 and later).
- **Target:** `research/artifacts/sk-free-4-finite-simple-shadows-2026-09-13-part1.md`, plus part 3 §1 for credit.
- **Method:** every step re-derived by hand. No other review of these claims was on main (tip 71c3695c55) when I started.

## 0. Verdicts

| claim | verdict |
|---|---|
| `kazhdan-marked-limits-eventually-uniform-expanders` (Theorem A) | **PASS** |
| `simple-lef-groups-are-limits-of-finite-simple-groups` (Theorem B, Proposition B3) | **PASS**. One wording fix (F-B3) to the artifact's classification step; the claim and route text are unaffected. |
| `lef-iff-subgroup-of-simple-kazhdan-all-approximants-expand` (Corollary B2) | **PASS** |

No FAIL and no GAP.

## 1. Theorem A (every finite approximation of a Kazhdan group expands)

**Import, checked at source.** Stalder, arXiv:0803.2592, e-print `main.tex`, fetched on MSI:
- l.158–160: "group is a quotient of a finitely presented Kazhdan group: \begin{theorem}[Shalom \cite{Sha}] Property (FH) defines an open subset in the space of marked groups."
- l.936–939, the bibitem: "Y. Shalom. Rigidity of commensurators and irreducible lattices. Invent. Math., 141(1):1--54, 2000."
- (FH) is equivalent to (T) for countable groups (Delorme–Guichardet); Stalder works with (FH). This matches the import node `fpbs-shalom-property-t-is-open` and its citation route.
- How the proof uses openness: let R_n ⊆ N = ker(F(T) → G) be finite, increasing, with union N. Then F(T)/⟨⟨R_n⟩⟩ → (G,T) in the space of marked groups, so for large n this group lies in the open Kazhdan neighbourhood. Put R_0 = R_n.

**Steps re-derived.**
1. **Quotients.** Every ρ ∈ R_0 has length ≤ r and is trivial in G, hence trivial in Q_k for k ≥ k_r. So t ↦ t_k extends to an epimorphism Γ_0 → Q_k that respects the markings.
2. **Kazhdan transfer.** Pull ℓ²(Q_k) back to Γ_0. The Q_k-invariant vectors are the constants, because T_k generates Q_k, and ℓ²_0(Q_k) is their orthogonal complement. So for unit ξ ∈ ℓ²_0(Q_k), max_{t∈T} ‖λ(t)ξ − ξ‖ ≥ κ, with κ a Kazhdan constant of (Γ_0,T).
3. **Gap.** For unit ξ, ‖λ(s)ξ − ξ‖² = 2 − 2Re⟨λ(s)ξ,ξ⟩. So ⟨(I−M)ξ,ξ⟩ = (2|T^±|)^{-1} Σ_{s∈T^±} ‖λ(s)ξ − ξ‖² ≥ κ²/(2|T^±|).
   - M is self-adjoint because T^± is closed under inverses.
   - For k ≥ k_2, distinct elements of T^± have distinct images, so |T_k^±| = |T^±|.
4. **Size.** For k ≥ k_{2r}, the ball B_T(r) of G injects into Q_k, since g ≠ h in the ball differ by a nonrelator of length ≤ 2r. G is infinite, so |Q_k| → ∞. Cheeger's inequality turns the uniform gap on |T^±|-regular graphs into uniform edge expansion.

**Quantifiers (asked by main).**
- κ and R_0 depend only on (G,T), not on the approximating sequence. The order "κ, R_0; then any sequence; then all large k" is as stated.
- κ is a Kazhdan constant of the finitely presented cover Γ_0. It may be smaller than the best Kazhdan constant of (G,T); the claim asserts only that some κ > 0 exists.
- G need not be finitely presented. The approximants need nothing beyond marked convergence.

**Model tests.**
- (Z,1), approximated by Z/n: (T) fails, and the cycles are not expanders.
- SL_3(Z) with its congruence quotients recovers Margulis' expanders.
- A finite G gives bounded |Q_k|, so no expander family, and the statement correctly asks G to be infinite for that part.

**Credit (part 3 §1).**
- Stalder's abstract (e-print l.116–117) matches part 3's quote verbatim.
- Kun, arXiv:1606.04471 (e-print fetched on MSI), l.32 reads "We prove Bowen's conjecture that every sofic approximation of a countable group with Kazhdan Property (T) is essentially a vertex-disjoint union of expander graphs." Part 3 quotes different wording ("every sequence of finite graphs that locally converges to the Cayley graph of a countably infinite group…"), probably from another version's abstract. The content agrees; if the note quotes Kun, use one version and say which.
- I agree with the folklore grading: credit Shalom and Margulis, and claim nothing new.

## 2. Theorem B (simple LEF groups are limits of finite simple groups)

**Steps re-derived.**
1. **Nontrivial approximants.** A generator nontrivial in G stays nontrivial in Q_k for k ≥ k_1. So maximal normal subgroups M_k exist, and Q_k/M_k is simple.
2. **Relators survive.** A relator of length ≤ r is trivial in Q_k, hence in any quotient.
3. **Nonrelators survive.**
   - For w ∈ W_r and t ∈ T, simplicity of G makes the normal closure of w all of G. So t = ∏_i h_i w^{ε_i} h_i^{-1} in G, and c_{w,t} is a relator of length L(w,t).
   - W_r is finite, so L_r = max L(w,t) is finite. For k ≥ k_{L_r}, every c_{w,t} holds in Q_k.
   - If w_k ∈ M_k, normality of M_k gives t_k ∈ M_k for all t, so Q_k = M_k, a contradiction. So w_k ∉ M_k.
   - The extra condition k ≥ k_r ("w nontrivial in Q_k") is implied and is harmless.
4. **Uniformity in the choice of M_k.** The bound k ≥ max(k_r, k_{L_r}) does not depend on M_k, so the conclusion holds for every choice of maximal normal subgroups.
5. **Nonabelian.** G is infinite simple, hence nonabelian, and generated by T. So some [t,t′] is nontrivial of length 4 and survives by step 3.
6. **Converse.** A marked limit of finite groups is LEF. For finitely generated groups this is the definition used in the artifact (Vershik–Gordon).

**Where simplicity enters.** Only in step 3, the normal closure of w is G.

**Model test.** G = Z, approximated by Z/p^a, is not simple. Its maximal-normal quotients are all Z/p, which do not converge to Z. The proof breaks exactly at step 3: the normal closure of w = t^p is not Z.

## 3. Proposition B3 (unbounded rank)

**Steps re-derived.**
- **Ultraproduct.** A word is trivial in ∏_ω Q_k iff it is trivial for ω-almost all k, and cofinite sets belong to ω. By marked convergence this happens iff the word is trivial in G, so G ↪ ∏_ω Q_k.
- **Linearity.** If Q_k ≤ GL_d(K_k) for ω-almost all k, then ∏_ω GL_d(K_k) = GL_d(∏_ω K_k), and ∏_ω K_k is a field (Łoś). A finitely generated linear group is residually finite (Mal'cev). An infinite simple group is not.
- **Classification step.** For each ℓ, only finitely many indices k have Q_k sporadic, alternating of degree ≤ ℓ, or of Lie type of rank ≤ ℓ, because each such group embeds in GL_{c(ℓ)} of a field. So the Q_k are eventually alternating of unbounded degree or of Lie type of unbounded rank. An isomorphism type repeated infinitely often is excluded by the same argument.

**F-B3 (wording, artifact only).** Part 1 §3 justifies the bounded embedding "through the adjoint representation of the corresponding algebraic group". In bad characteristic the Lie-algebra adjoint representation is not the safest justification. Replace it with:
> "a simple group of Lie type of rank ℓ acts faithfully on the projective space of a module of dimension m ≤ c(ℓ) (the natural module for classical types, a minimal module for exceptional and twisted types), so it embeds in PGL_m(K), and PGL_m(K) embeds in GL_{m²}(K) through conjugation on M_m(K)."

Neither the claim nor the route text uses the adjoint wording, so no node change is needed.

## 4. Corollaries B1 and B2

**B1.** It is Theorem B plus Theorem A, applied to any marking. The hypotheses (infinite, finitely generated, simple, Kazhdan, LEF) are exactly those both theorems need.

**B2.**
- (ii) ⇒ (i): a marked limit of finite groups is LEF, and LEF passes to finitely generated subgroups.
- (i) ⇒ (ii): take the host from `lef-groups-embed-in-simple-kazhdan-lef-groups`. That node is reviewed PASS by sk-verify-3 and sk-verify-4, and it is rev3's Corollary 2, which both rev3 referees re-derived. Then apply B1. Expansion needs |Q_k| → ∞, which holds because the host is infinite.

The route's `requires:` list matches these three inputs.

## 5. Note relevance (for main)

B2 gets "a marked limit of finite simple groups, every finite approximation of which expands, for every marking" from the reviewed LEF host alone.
- Cost: about six lines and a citation of Shalom.
- It needs no configuration models, but does not name the type SL_N(F_2).
- Rev4 decision 96 uses the configuration-space models so that the approximants are SL_N(F_2) on a fixed marking. B2 is a different trade-off: expansion for every marking and every approximating sequence, but no control of the type.
- Proposition B3 shows the approximants must have unbounded rank either way.
