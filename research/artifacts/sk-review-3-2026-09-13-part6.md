# SK review 3, part 6: every f.g. LEF group lies in an infinite simple Kazhdan LEF group; Whitehead firewall and repaired routes

Lane `sk-verify-3`, 2026-09-13. Queue items 11–15. Main read at tip `232c77f169`. Every step below was re-derived.

# A. Lamplighter crossed products (sk-universal-embedding-b, queue items 14–15)

Artifact: `research/artifacts/sk-universal-embedding-b-lamplighter-2026-09-13.md`.

## A0. Verdicts

| claim | route | verdict |
|---|---|---|
| `lamplighter-bernoulli-crossed-products-simple-kazhdan-lef` (Theorem 5) | `-proof` | PASS |
| `lef-groups-embed-in-simple-kazhdan-lef-groups` (Corollary 6) | `lef-groups-embed-in-simple-kazhdan-lef-groups-proof` | PASS. Display owed: the claim body still reads "OPEN" with Attempts written before the route. The owner should restate it as established. |

So a finitely generated group is LEF if and only if it is a subgroup of an infinite finitely generated simple group with property (T) that is LEF. This supersedes the residually finite case (part 3 §A), which it contains.

## A1. Dynamics and ring (Lemmas 1–2)

- **The group.** δaδ^(−1) is the flip at δ, so L = {x ↦ δ·x + f} ≅ Z/2 ≀ Δ, acting faithfully.
- **Finite generation.** u_δ p u_δ^(−1) = 1_(δ·[x(e)=1]) = 1_([x(δ)=1]).
- **Minimality.** The orbit of x contains x + ⊕_Δ Z/2, which is dense.
- **Topological freeness.**
  - δ = e with f ≠ 0 has no fixed point.
  - δ ≠ e: for a cylinder on W, Δ infinite gives h with h, δ^(−1)h ∉ W ∪ supp f. These are distinct coordinates, and x(h) ≠ x(δ^(−1)h) gives (ℓx)(h) = x(δ^(−1)h) ≠ x(h). So Fix(ℓ) has empty interior.
- **Simplicity.**
  - L is countable, so free points are dense by Baire.
  - A free x₀ with f_1(x₀) = 1 and a clopen U with U ∩ ℓU = ∅ on the support give 1_U r 1_U = 1_U. Minimality gives 1 ∈ I.
- **Centre.** [1_V, r] = Σ f_ℓ(1_V − 1_(ℓV))u_ℓ kills f_ℓ off Fix(ℓ^(−1)). A clopen set with empty interior is empty. Invariance makes f_1 constant.

PASS.

## A2. Matricial models (Lemma 3, Proposition 4)

- **Letters.**
  - σ_s(c,q) = (c, qφ(s)^(−1)) and φ(s)^(−1) = φ(s^(−1)) on large balls. So x_(σ_s z)(h) = c(qφ(s^(−1)h)) = (s·x_z)(h).
  - σ_a adds 1_q. Injectivity of φ gives [qφ(h) = q] = [h = e], so x_(σ_a z) = a·x_z.
- **Composition.**
  - ℓℓ′ = (δδ′, δ·f′ + f).
  - σ_ℓσ_(ℓ′)(c,q) has second coordinate qφ(δ′^(−1))φ(δ^(−1)) = qφ((δδ′)^(−1)).
  - Its first coordinate adds 1_(qφ(δ′^(−1))φ(h′)) for h′ ∈ supp f′. This equals 1_(qφ((δδ′)^(−1))φ(δh′)) by partial multiplicativity.
  - The terms from supp f match directly, and cancellation mod 2 respects the sum of supports.
  - So σ_(ℓℓ′) = σ_ℓσ_(ℓ′) on bounded words for large n.
- **Legality.** Every configuration is legal, so D_n(f) = diag f(x_z) is defined on any extension.
- **Diagonal.** P_σ D(f) P_σ^(−1) δ_(σz) = f(x_z)δ_(σz). Also x_(σ_ℓ z) = ℓ·x_z on B_(n/2), so (f∘ℓ^(−1))(x_(σ_ℓ z)) = f(x_z) once n ≫ ρ, r.
- **Conclusion.** π_n is exactly additive and multiplicative on any fixed finite set for ω-almost all n, and π_n(1) = I. The resulting unital ring homomorphism into ∏_ω M_(N_n)(F_2) is injective by simplicity.

PASS.

## A3. Theorem 5 and Corollary 6

- **Simplicity.**
  - The transformation groupoid is Hausdorff, ample, minimal and effective (topological freeness) with Cantor unit space, so `steinberg-elementary-groups-are-simple-mod-centre` applies. This is reviewed PASS twice; part 1 §1 checked the Lean criterion at source.
  - Z(G) ⊆ Z(R)^× I = {I}.
- **(T).** EJZ.
- **LEF.** Through the ultraproduct.
- **Embedding.**
  - diag(a,a^(−1))·diag(b,b^(−1))·diag((ab)^(−1),ab) = diag(1, a^(−1)b^(−1)ab). This gives diag(1,c) ∈ E_2 for commutators c.
  - Conjugating by e_12(1)e_21(1)e_12(1) moves c to the first slot; signs cancel under conjugation.
  - c ↦ diag(c,1,…,1) is an injective homomorphism on [R^×, R^×] ⊇ u_([L,L]).
- **Corollary 6.**
  - Overgroup: `rf-groups-lie-in-derived-subgroups-of-rf-groups` (2), reviewed PASS in part 3 §A2.
  - Δ × Z is f.g., LEF and infinite, with derived subgroup [Δ,Δ] × 1 ⊇ Γ.
  - [Δ×Z, Δ×Z] ≤ [L,L], and γ ↦ u_γ is injective.
  - The converse holds because subgroups of LEF groups are LEF.

PASS.

## A4. Scope and credit

- The action is not free, since δ-periodic points exist. So the note's own tower proof (partitions with C ∩ gC = ∅) does not apply here, and simplicity needs the Steinberg criterion (Lean-certified, unpublished) or an adapted argument. This matters if the corollary enters the note.
- Novelty check is bounded (a Cairn grep only). sk-novelty should search for "every LEF group embeds in a simple LEF group" without (T), e.g. topological full groups and Kionke–Schesler-type telescopes.

# B. Whitehead firewall and repaired routes (sk-subgroups, queue items 11–13)

Artifact: `research/artifacts/sk-subgroups-full-group-inside-2026-09-13-part2.md` §4 (landed 8dce9c3906).

## B0. Verdicts

| node | verdict |
|---|---|
| `whitehead-diagonal-map-is-not-multiplicative` (with route `whitehead-diagonal-not-multiplicative-proof`), plus its new `invalidates:` entries | PASS |
| route `simple-kazhdan-linear-sofic-non-lef-via-lef-converse` → `simple-kazhdan-linear-sofic-non-lef-group-exists` | PASS for the restated scope (non-LEF for N ≥ 4; S_N = EL_N for q = 2) |
| route `rank-modelled-non-lef-el-via-lef-converse` → `rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group` | PASS (existential, realized at N = 4) |

## B1. Firewall

- w(X)w(Y) = diag(XY, X^(−1)Y^(−1)) and w(XY) = diag(XY, Y^(−1)X^(−1)). They agree iff XY = YX.
- Witness in [[T]]: with U, TU, T²U disjoint, τ fixes U, so στ(U) = σ(U) = TU. But τσ(U) = τ(TU) = T²U. So σ and τ do not commute, and their units do not commute, since γ ↦ a_γ is injective.
- The three routes it now invalidates each apply ι(g) = diag(u_g, u_g^(−1), 1) as a homomorphism on nonabelian groups (Γ_p, or general Γ). The invalidations are correct and the firewall claim is established.
- What survives:
  - diag(θ(g),1,…,1) is a homomorphism, and diag([a,b],1) = diag(a,a^(−1))·diag(b,b^(−1))·diag((ba)^(−1),ba) ∈ E_2.
  - The note's Z-case map diag(u^n, u^(−n), 1) is multiplicative, because Z is abelian.

PASS.

## B2. Repaired non-LEF routes

- **Step 6, simple-kazhdan route (step 3 of the rank-modelled route).**
  - A LEF EL_N(R) with N ≥ 4 makes R a LEF ring (`lef-elementary-groups-force-lef-rings`, PASS, part 1 §2).
  - R is countable and simple, so it is exactly matricial over finite fields (`simple-lef-rings-are-exactly-matricial`, PASS).
  - Then GL_1(R) = R^× is LEF (`exactly-matricial-rings-have-lef-general-linear-groups`, stated for every N ≥ 1).
  - γ ↦ u_γ embeds Γ_p in R^×. Γ_p is finitely presented and not RF, since c_p dies in every finite quotient, so it is not LEF. Contradiction.
- **Step 7.** Over F_2, Z(EL_N(R)) ⊆ Z(R)^× I = {I}, so S_N = EL_N(R).
- **Statement fidelity.**
  - `simple-kazhdan-linear-sofic-non-lef-group-exists` now asserts non-LEF only for N ≥ 4, and for S_N only when q = 2. The repaired route proves exactly that.
  - `rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group` is existential ("some N ≥ 3"), and N = 4 realizes it.
- Steps 1–5 (Abels–Prüfer, Gao–Jackson–Seward subflow, Steinberg simplicity, EJZ, linear soficity) are unchanged from the earlier route, which was reviewed PASS (un-verify-3, part 3). I did not re-review them.
- Rank 3 stays open, as the nodes say.

PASS.
