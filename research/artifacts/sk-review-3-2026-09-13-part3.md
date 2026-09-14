# SK review 3, part 3: the residually finite embedding theorem, and diagonal-preserving rigidity

Lane `sk-verify-3`, 2026-09-13. Every step below was re-derived.

# A. Priority 1: every f.g. residually finite group lies in an infinite simple Kazhdan LEF group (queue item 7)

Main read at tip `45a8a34e9e`. Artifact: `research/artifacts/sk-universal-embedding-a-rf-embedding-2026-09-13.md` (landed 3bcc003284).

## A0. Verdicts

| claim | route | verdict |
|---|---|---|
| `rf-groups-embed-in-simple-kazhdan-lef-groups` (Theorem E) | `rf-groups-embed-in-simple-kazhdan-lef-groups-proof` | PASS |
| `rf-groups-lie-in-derived-subgroups-of-rf-groups` (Lemma 2, RF and LEF cases) | `-proof` | PASS |
| `ore-even-permutations-are-commutators` | `-citation` (Ore 1951 Thm 1, JSTOR scan) | PASS as import (primary not re-read by me) |
| `rf-toeplitz-subshifts-act-freely` (Lemma 3) | `-proof` | PASS |
| `shift-unit-of-subshift-crossed-product-is-not-elementary` (Prop 1) | `-proof` | PASS |
| artifact §4, Proposition 5 (tower proof over Δ), not a `requires` of the route | — | PASS |

No FAIL. The theorem is ready to be a corollary of the note, with the credit noted in A6.

## A1. Proposition 1 (firewall)

- **Representation.** R acts on V = ⊕_(t∈Z) kδ_t by uδ_t = δ_(t+1) and fδ_t = f(T^t x)δ_t. It respects the relation, since u f u^(−1) δ_t = f(T^(t−1)x) δ_t = (f∘T^(−1))(T^t x) δ_t.
- **Fredholm.** Propagation is bounded, so P a(1−P) has finite rank. P a^(−1) P · P a P = P − P a^(−1)(1−P) a P, so PaP is invertible modulo finite rank.
- **Index is a homomorphism.** The algebraic index over a field is additive and invariant under finite-rank perturbation, so ind: GL_n(R) → Z is a homomorphism.
- **Elementary matrices.** P e_ij(r) P = P + N with N² = P rE_ij P rE_ij P = 0, since P acts coordinatewise and E_ijE_ij = 0. So ind(e_ij(r)) = 0.
- **The shift.** P diag(u,1,…,1) P is the unilateral shift, with cokernel kδ_0, so ind = −1.

PASS.

## A2. Lemma 2 (overgroup of commutators)

**RF case.**
- λ_n(γ) on Γ/Γ_n × {1,2} has its cycles in equal pairs, so sign = sign² = +1.
- ρ = (λ_n) is injective, because ∩Γ_n = {e}.
- Choosing a_s, b_s coordinatewise (Ore) gives ρ(s) = [a_s,b_s] in P = ∏ Sym(Ω_n).
- Δ = ⟨ρ(S), a_s, b_s⟩ is f.g., and it is RF as a subgroup of a product of finite groups.
- ρ(Γ) = ⟨ρ(S)⟩ ≤ [Δ,Δ], and Δ is infinite if Γ is.

**LEF case.**
- Γ ↪ ∏_ω F_n; doubling the regular representations lands in even permutations.
- Choosing coordinatewise commutators gives a f.g. subgroup of an algebraic ultraproduct of finite groups, which is LEF.

PASS.

## A3. Lemma 3 (freeness at every point)

- (g·x)(h) = x(g^(−1)h), so g·x is constant on every Γ_m-coset K ≠ gC_m, because g^(−1)K ≠ C_m. It is non-constant on gC_m (F2).
- **Limits.** For y = lim g_k·x, fix a residue g_kΓ_(m+1) along a subsequence.
  - This fixes D = g_kC_m and E_1, E_0 = g_k c_(1/0) Γ_(m+1) = g_k Γ_(m+1) c_(1/0), using normality.
  - Pointwise limits preserve constancy on the other cosets, and y ≡ 1 on E_1, y ≡ 0 on E_0.
- **Uniqueness and nesting.** D_m(y) is intrinsic to y, so subsequences for different m need not agree. A Γ_(m+1)-coset inside a constant Γ_m-coset is constant, which gives nesting.
- **Freeness.** g·y = y gives gD_m(y) = D_m(y), so c^(−1)gc ∈ Γ_m and g ∈ Γ_m, for every m. Hence g = e.

PASS.

## A4. Theorem E route (the coordinator's checkpoints)

- **Overgroup.** A2. Finite Γ is replaced by Γ × Z, which is f.g., RF and infinite.
- **Envelope.**
  - Corollary T (`residually-finite-group-toeplitz-elementary-groups-lef-kazhdan`, reviewed PASS twice) applies with q = 2, N = 3 to Δ, which is f.g., infinite and RF.
  - Z(EL_3(R)) ≤ F_2^× I = {I}, so G = EL_3(R) is itself infinite, f.g., simple, Kazhdan and LEF.
- **diag([a,b],1,1) ∈ E_3.**
  - w(c) = e_12(c) e_21(−c^(−1)) e_12(c): computing the product gives [[0,c],[−c^(−1),0]], and w(c)w(−1) = diag(c, c^(−1)), with the entries checked over a noncommutative ring.
  - diag(a,a^(−1)) · diag(b,b^(−1)) · diag((ba)^(−1), ba) = diag(ab a^(−1)b^(−1), a^(−1)b^(−1)ba) = diag([a,b], 1).
- **Injective homomorphism on [Δ,Δ].**
  - δ ↦ u_δ is an injective homomorphism Δ → R^×, since the u_δ are distinct basis elements of the crossed product.
  - For ρ(γ) = ∏[a_i,b_i] in Δ, u_(ρ(γ)) = ∏[u_(a_i), u_(b_i)]. So ψ(γ) = diag(u_(ρ(γ)),1,1) = ∏ diag([u_(a_i),u_(b_i)],1,1) ∈ E_3(R).
  - ψ is a homomorphism because it is the composite of homomorphisms, and it is injective.

PASS.

## A5. Proposition 5 (the note's tower proof rerun over Δ)

- **Ring simplicity, centre, Z(G) = 1.** Freeness at a point where f_e = 1 gives a clopen U with gU ∩ U = ∅ for the finitely many g ∈ supp ∖ {e}, and e_U r e_U = e_U. Separating x from g^(−1)x kills f_g, g ≠ e. u_s-invariance plus minimality makes f_e constant.
- **LEF.**
  - D(f)δ_(hΔ_M) = f(h·p) is well defined, since p is Δ_M-invariant and every W-window of h·p lies in L_W(X).
  - P_g D(f) P_g^(−1) δ_(hΔ_M) = f(g^(−1)h·p) δ_(hΔ_M) = D(f∘g^(−1)) δ_(hΔ_M), and P_gP_(g′) = P_(gg′) because Δ acts genuinely on Δ/Δ_M.
  - Coverage keeps coefficients nonzero.
  - If g ≠ g′ ∈ F and gc = g′c for some coset c = hΔ_M, then g^(−1)g′ ∈ Δ_M. So Δ_M ∩ F^(−1)F = {e} separates the P_g.
- **Towers.**
  - E_(β,β′)(W)E_(δ,δ′)(W′) = e_(βW) e_(ββ′^(−1)δW′) u_(ββ′^(−1)δδ′^(−1)). This equals E_(β,δ′)(W∩W′) if β′ = δ. Otherwise it lies inside β(U ∩ β′^(−1)δU) = ∅.
  - The levels βU are pairwise disjoint.
- **Absorption.**
  - f u_γ · E_(β,β′)(W) = E_(γβ,β′)(W_1), and E_(β,β′)(W) · f′ u_γ = e_(βW) (f′∘β′β^(−1)) u_(ββ′^(−1)γ) = E_(β,γ^(−1)β′)(W_2).
  - With entries of g and g^(−1) supported in B_w, the commutator k lies in M_3 of the B_(w+1)-tower. That tower is disjoint once C ∩ gC = ∅ for e ≠ g ∈ B_(2w+2), which is where freeness at EVERY point is used, through compactness.
- **Generators.** e_C = E_(e,e)(C) and e_C u_s = E_(e,s^(−1))(C) lie in the B_1-tower over U = C, and their sums give 1, u_s^(±1) and the letter indicators.
- **In-block transvections.** ρ = E_(β,β′)(W), σ = E_(β′,β′)(W), β ≠ β′: ρσ = ρ, σρ = 0, ρσρ = 0, so the commutator is I + ρE_pp.
- **Rest.** d = 3|B_(w+1)| ≥ 6. The corner function κ, the constant piece κ_0 ≠ I on W, [k,H_W] ⊆ N ∩ H_W, and the level ideal carry over verbatim.

PASS.

## A6. Credit and bounds

- Kionke–Schesler Thm 1.2 is quoted from sk-questions-ggt's literature artifact. I did not read it at source, and sk-citations should confirm it before it enters the note.
- The novelty search is bounded (two web searches plus sk-questions-ggt part 1). Embeddings into simple Kazhdan groups without approximation properties were not searched.
- Ore 1951 is an import from a scan read by the lane. The statement is the well-known theorem.

# B. Diagonal-preserving rigidity (sk-rigidity-intrinsic, queue items 3–5)

Main read at tip `82eafe28dd`. Artifact: `research/artifacts/sk-rigidity-intrinsic-reconstruction-2026-09-13-part1.md`.

## Verdicts

| claim | route | verdict |
|---|---|---|
| `locally-constant-simple-group-normal-subgroups-are-open-sets` (Lemma B) | `locally-constant-simple-group-normal-subgroups-proof` | PASS |
| `subshift-elementary-group-rigid-supports-are-mutual-centralizers` (Lemma C) | `subshift-el3-rigid-supports-proof` | PASS |
| `subshift-elementary-group-diagonal-iso-gives-flip-conjugacy` (Theorem A) | `subshift-el3-diagonal-iso-flip-conjugacy-proof` | PASS |

Not reviewed: artifact §5 (F3), the claim that clopen sets of equal K^0 class are [[T]]-equidecomposable, and the §6 remark over F_q.

## 1. Lemma B: normal subgroups of LC(Z,Q), Q finite nonabelian simple

- Let f ≡ x ≠ 1 on a clopen V, and let g_y be y on V and 1 elsewhere. Then [f,g_y] is [x,y] on V and 1 elsewhere, and it lies in N.
- ⟨[x,Q]⟩ is normal: y[x,z]y⁻¹ = [x,y]⁻¹[x,yz]. It is nontrivial because Z(Q) = 1, so it is Q.
- The same holds on every clopen V′ ⊆ V, so N ⊇ N_V. Then N_(supp f) ≤ N by partitioning supp f.
- **N = N_O** for O = ⋃{V : N_V ≤ N}. Supports are compact, so a finite subcover refined to disjoint clopen pieces writes f as a product.
- **Uniqueness.** If x ∈ O ∖ O′, a function supported on a clopen V ∋ x inside O is not in N_O′.
- **Points.** Maximal proper open sets are Z ∖ {z}. The hull–kernel basic set {z : N_O ⊄ N_(Z∖{z})} = O.
- **Homeomorphism.** An isomorphism α induces an order isomorphism of the lattices of open sets, hence a homeomorphism h with α(N_O) = N_(h(O)).
- **Supports.** The normal closure of f is N_(supp f), so supp α(f) = h(supp f).

PASS.

Credit lead (recalled, not read at source): these are Boolean powers of a finite simple group. The ideal-lattice description of their normal subgroups appears in the Boolean-power literature (e.g. Apps, *Boolean powers of groups*, 1982). The node says folklore; sk-novelty may want the citation.

## 2. Lemma C: rigid supports

**(C1).**
- e_ij(r) lies in G_U for r ∈ e_U R e_U.
- The span is multiplicatively closed, by (g−I)(h−I) = (gh−I) − (g−I) − (h−I), since G_U is a subgroup.
- E_ij r · E_ji s = E_ii rs, and e_U lies in the corner, so the span is M_3(e_U R e_U).

**Corner centre.**
- c = Σ f_j u^j central in e_U R e_U has supp f_j ⊆ U ∩ T^jU.
- For clopen V ⊆ U, e_V c − c e_V = Σ f_j(e_V − e_(T^jV))u^j.
- Separating x from T^(−j)x inside U kills f_j for j ≠ 0.
- Commuting with e_(U∩T^jU)u^j gives f_0(y) = f_0(T^(−j)y) whenever y, T^(−j)y ∈ U.
- f_0 is constant on the dense set U ∩ (orbit) and locally constant, so it is constant.
- Z = F_2e_U, and LC(U) is maximal commutative in the corner.

**(C2).**
- h centralizing G_U commutes with E_U, and ehe is central in M_3(corner), since (ehe)x = hx = xh = x(ehe).
- So ehe = cE_U with c ∈ F_2, and invertibility gives c = 1.

**(C3).**
- span GL_3(F_2) is an algebra containing E_ij = e_ij(1) − I, hence all of M_3(F_2).
- span(GL_3(F_2) − I) is a nonzero two-sided ideal, so it equals M_3(F_2).
- A centralizer of L_(X∖U) is block diagonal with corner cI_3, c ∈ LC(X∖U,F_2) by maximal commutativity, and invertibility gives c = e_(X∖U).

**(C4).**
- Normalizers preserve the span M_3(e_U R e_U) and so fix its unit E_U; commuting with E_U preserves I + M_3(corner).
- The commutant of {e_U I} in M_3(R) is M_3(C_R(A)) = M_3(A), and GL_3(A) = EL_3(A) ≤ G, since A is a directed union of products of F_2.

**(C5).**
- span L = M_3(A), so N_G(L) normalizes Z(M_3(A)) = D. Stone duality gives φ.
- g_ij f = (f∘φ^(−1))g_ij forces c_n(f∘T^(−n) − f∘φ^(−1)) = 0, so φ^(−1) = T^(−n) on supp c_n.
- The supports cover X, since otherwise e_Vg = 0 on a clopen V ≠ ∅. So φ ∈ [[T]].
- Lower bound:
  - Whitehead: w(a)w(−1) = diag(a,a^(−1)).
  - The commutator formula diag([b,c],1,1) = diag(b,b^(−1),1)·diag(c,1,c^(−1))·diag(b^(−1),b,1)·diag(c^(−1),1,c) checks coordinatewise.
  - γ ↦ a_γ is a homomorphism with a_γ f a_γ^(−1) = f∘γ^(−1), so [[T]]′ ≤ Γ_X.
- Compatibility: g e_V(l−I)g^(−1) = e_(φV) g(l−I)g^(−1).

PASS.

## 3. Theorem A: diagonal-preserving isomorphisms and flip conjugacy

**(⇒).**
- Lemma B with Q = GL_3(F_2), simple of order 168, gives h. For g ∈ N(L_X) inducing φ, α(g) maps α(N_z) = N_(hz) onto N_(hφz). So h Γ_X h^(−1) = Γ_Y.
- **Piecewise closure.**
  - Take V, T^nV, T^(2n)V disjoint. τ_1 = (01) and τ_2 = (02) on the levels.
  - Composing right to left, [τ_1,τ_2] = τ_1τ_2τ_1τ_2 sends 0→1→2→0, so it equals T^n on V and lies in [[T]]′.
  - Compactness gives a finite partition, so P(Γ_X) = [[T]].
- P is defined from the action, so h[[T]]h^(−1) = [[S]]. Then `topological-full-groups-determine-flip-conjugacy` gives flip conjugacy.
  - That node has a `-citation` route with verbatim quotes: Matui arXiv:math/0404117v3 Thm 2.8(ii), citing GPS 1999 Cor 4.4, and Bezuglyi–Medynets arXiv:math/0611173v1 Thm 5.13. Both were read from the arXiv HTML, not the journal versions.

**(⇐).** ψT = S^εψ inverts to T^(−1)ψ^(−1) = ψ^(−1)S^(−ε). So f u^j ↦ (f∘ψ^(−1))u^(εj) respects the crossed-product relation and maps A_X onto A_Y.

PASS.

## 4. For the note

This is rigidity for isomorphisms that preserve the diagonal subgroup. It does not classify the groups G_X, and the lane marks the classification OPEN. It supplies neither "continuum many" nor a replacement for the Turing-degree corollary. At most it would earn a remark that the diagonal subgroup, when preserved, recovers X up to flip conjugacy, and that remark would add the GPS citation.
