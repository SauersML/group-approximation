# EX review wave 2, part 3: detection for Z/p-actions and the O_2 dynamics behind it (2026-09-13)

Lane `ex-verify2-analysis`. Verdict legend as in `ex-review2-analysis-2026-09-13.md` §0.

**Landings.**
- ex-uct-detection-phantom: `04778a8ab7`, `b6aadbc601`, `8dbc1d62a5`, `b2553dd4c7` and `fd6537b1ac`.
- ex-uct-detection-prove: `c2d71357cf`, `7cb0dbd7bb`, `35f6395dee`, `6292a13950`, `95513b89cb`, `8a965d4f6e`,
  `3b0ebd5c8a` and `39e6a004a7`.

**Sources re-checked** on MSI, in the lanes' ghostscript extractions under
`/scratch.global/sauer354/ex/ex-uct-detection-{phantom,prove}/`:
- Meyer, arXiv:1906.11163v3, Lemma 4.2: matches the citation route verbatim.
- Meyer--Nadareishvili, arXiv:2406.11787v2: both "We do not know whether" sentences are there (introduction, and
  before Corollary 3.5).
- Gabe--Szabó, arXiv:2205.04933: Theorem 5.8 and the opening "the 'if' part is clear" match verbatim. So do
  Corollary 6.4(i), "every invertible element x ∈ KK^G(α, β) lifts to a conjugacy", and Corollary 6.4(ii), with
  the condition KK^G(ι_A) ⊗ x = KK^G(ι_B). Proposition 3.15 is present.
- Szabó, arXiv:1804.04411: Corollary B is present. Its statement was not re-grepped.
- Not re-read here: Köhler's Theorems 2.9 and 2.10 (as quoted in arXiv:2604.12529v2), Szabó arXiv:1509.08380 and
  Hirshberg--Winter. The extractions exist; the quotes are consistent with the uses.

## 3.1 Structure

- **The open questions stay open.** `zp-restriction-and-crossed-product-detect-kk-g-contractibility` and
  `outer-zp-actions-on-o2-are-strongly-approximately-inner` are joined by two routes, each requiring the other. That
  is a 2-cycle, which correctly fires neither.
  - `nuclear-algebra-without-uct-exists` and `stw99-problem-ii-nuclear-uct` stay open; each route needs an open
    prerequisite.
- **Graph fix, landed `d16d59955a`.**
  - `zp-detection-iff-bootstrap-sufficiency-and-kk-g-generation-proof` had `requires: []`. But its (S) ⟹ (D) step uses
    item 1 of `bootstrap-zp-actions-realize-every-cyclotomic-k-module`, and both bootstrap steps use Köhler's
    Theorems 2.9 and 2.10.
  - Both claims are now under `requires`. Each is established by a `requires: []` route that does not depend on this
    claim, so no status changes.
  - The owner was told.
- **Borrowed facts.** Every other route in scope names its claim prerequisites. The literature facts marked "standard,
  not re-read" are ordinary tools, not claims: Kishimoto; Kirchberg--Phillips in KK form; Meyer--Nest triangulated
  structure; Baaj--Skandalis; Green--Julg; Cuntz comparison.

## 3.2 Literature imports: four PASS

- **`gabe-szabo-unital-uniqueness-theorem`: PASS.** The quotes were checked as above. Definition 1.15 with trivial
  cocycles gives ‖1 − u_t β_g(u_t)*‖ → 0.
- **`meyer-little-invariant-detects-zero-in-zp-bootstrap`: PASS.** Lemma 4.2 is verbatim. L_* = K_*(A ⋊ G) ⊕ K_*(Res A)
  by Green--Julg and Ind--Res.
- **`mn-cyclic-restrictions-detect-equivariant-bootstrap`: PASS.** The open converse is quoted verbatim. Theorem 2.1,
  Theorem 3.1 and Corollaries 3.2--3.3 are consistent with the text around those sentences, but were not re-grepped.
- **`kohler-uct-for-zp-equivariant-bootstrap`: PASS as an import, quotes not re-read.** It matches the reading by
  lane ex-uct of the same Theorems 2.9 and 2.10.

## 3.3 `zp-detection-equals-meyer-nadareishvili-sufficiency`: PASS

- **MN ⟹ Det.** Res D and D ⋊ G are 0, so both lie in B. MN gives D ∈ B^G, and L_*(D) = 0 with Meyer Lemma 4.2 gives
  D ≃ 0.
- **Det ⟹ MN.**
  - U(A) is exact (Theorem 2.9), so there is P ∈ B^G with U(P) ≅ U(A). Theorem 2.10 lifts the isomorphism to x.
  - The cone D has U(D) = 0, since U is stable homological. That includes K_*(Res D) and K_*(D ⋊ G).
  - Res and − ⋊ G are triangulated, and Res P, P ⋊ G ∈ B. B is closed under cones, so the UCT kills Res D and D ⋊ G.
  - Then Det(𝒞) with D ∈ 𝒞 makes x invertible.
- **𝒞 = nuclear.** P is chosen of type I. For nuclear P, x is an equivariantly semisplit extension with nuclear middle
  term, obtained by averaging a c.p. lift over finite G. So D can be taken nuclear.
- **UCT_G ⟺ UCT ∧ Det(nuclear).** (⟹) uses τA ∈ B^G and Res τA = A. (⟸) uses that Res A and A ⋊ G are nuclear.

## 3.4 `zp-restriction-trivial-splits-cellular-plus-phantom`: PASS

- **Step 1.** W = U_ω^{-1} gives an isomorphism of cycles (ℰ, φ∘α_ω, F) ≅ (ℰ_⋆, φ, F): it is B-linear, isometric,
  intertwines, and commutes with U_g because G is abelian. So θ is natural. Also θ^p = 1, θ is multiplicative on
  tensors, and θ = 1 on τX.
- **Step 2.** α_ω ⋊ G = Ad u_ω, since α_ω(a)u_g = u_ω a u_g u_ω* for abelian G. V(y) = u_ω y shifts the dual action by
  the character ω̂, so j_G(θ_A) = ω̂^{±1}·1 in KK^Ĝ. Forgetting the action gives Φ(θ_A) = 1.
- **Step 3.**
  - (⟸) Φ(1 − θ) = 0 is a unit only on a zero object.
  - (⟹) The cyclotomic node for Ĝ makes 1 − ψ a unit for every nontrivial character, since 1 − ζ^k ∈ Z[ζ_p, 1/p]^×.
    Baaj--Skandalis descent is an isomorphism compatible with products.
- **Step 4.** (θ − 1)N(θ) = 0 gives e = N(θ)/p idempotent and central, with θe = e. On (1 − e)E the relation N(θ) = 0
  makes 1 − θ a unit, so the crossed product vanishes.
- **Step 5.**
  - t_1 and t_2 commute and have order p, so e_diag = N(t_1 t_2^{-1})/p is idempotent, and ε∘e_diag = ε by
    naturality of the counit.
  - Φ(τX) = ⊕_k X_k, with Φ(t_1) cyclic and Φ(ε) = b^k on X_k. On the e_diag-image, Φ(ε) is multiplication by p.
- **Step 6.**
  - The cone N has Res N = 0 and ΦN = 0.
  - (θ − 1)_N factors through π and i, so its square is 0. It is also a unit (Step 3), so KK^G(N, N) = 0.
- **Steps 7--9.** Detection kills (1 − e)E, and its nuclear case goes through the telescope. Retract closure of B^G
  plus Lemma 4.2 give item 5. For item 6, Z[ζ_p, 1/p] is étale Galois over Z[1/p], so O ⊗ O ≅ ∏_σ O, and ζσ(ζ) = 1
  iff σ(ζ) = ζ^{-1}.

## 3.5 `zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner`: PASS

- **Item 1.** Theorem 5.8 applies to (α_ω, 1) and (id, 1) into (O_2, α): G is finite, hence exact and amenable, and α
  is outer, hence isometrically shift-absorbing.
  - Averaging: ‖E(u_t) − u_t‖ ≤ max_g ‖α_g(u_t) − u_t‖ → 0.
  - The polar part w_t of E(u_t) is a continuous unitary path in O_2^α with ‖w_t − u_t‖ → 0.
  - Ad(w_t) is isometric, so pointwise limits compose. That gives Izumi's strong approximate innerness as quoted in
    `izumi-rokhlin-approximately-representable-duality`, Definition 4.13.
- **Item 4.** Theorem D gives (B, β) on O_2 ⊗ K.
  - B^β is a hereditary corner of B ⋊ G, which is simple and purely infinite by outerness. So it contains a
    projection q, and qBq ≅ O_2.
  - The invariant full corner is a KK^G-equivalence, and naturality of θ transfers θ = 1.
- **Items 2, 3 and 5** follow from items 4--5 of the splitting theorem and Izumi's Theorem 4.6 as imported.

## 3.6 `outer-actions-on-o2-kk-g-contractible-iff-rokhlin`: PASS

- **Item 1.** Hirshberg--Winter Theorem 3.3 gives O_2 ⊆ (A_∞ ∩ A′)^α. Szabó Corollary 3.8, (iii) ⟹ (ii), gives
  α ≃_cc α ⊗ id_{O_2}. Then id_{τO_2} = 0 and bilinearity make id = 0.
- **Item 2.**
  - Rokhlin implies outer, since e_g = u e_1 u* = e_1 would contradict orthogonality.
  - Two contractible isometrically shift-absorbing unital actions have x = 0 invertible and KK^G(ι) = 0 on both
    sides. Corollary 6.4(ii), checked verbatim, gives a conjugacy with the model id ⊗ μ_G.
- **Item 3.** E = D ⊗ K(H) + C*(s_1, s_2), with fixed Cuntz isometries in M(D ⊗ K(H)), is unital, separable and nuclear.
  - It is a split extension of τO_2 by D ⊗ K(H): O_2 is simple and meets the ideal trivially.
  - Split exactness gives E ≃ D ⊕ τO_2 ≃ D. The unital Theorem 3.13 plus Kirchberg--Phillips give a unital outer
    action on O_2.
- **Item 4.** O_2 ⋊_α G ≅ O_2, and α̂ Rokhlin gives α̂ ≃ 0 by item 1. Takai duality then gives α ≃ 0.
- **Item 5.** Szabó arXiv:1804.04411 Corollary B, for finite G with N = 1 and the strongly self-absorbing id_{O_2}.
- **Credit.** The lane says item 2 is a direct application of Gabe--Szabó and that the explicit statement was not
  found in what it read. That is correctly hedged.

## 3.7 `o2-rokhlin-iff-unit-vanishes-in-fixed-central-sequences`: PASS

- **Item 1.** Szabó Theorem 5.15(2) gives α ≅ α ⊗ γ with γ quasi-free from λ ⊗ 1, and Theorem 3.7 embeds (O_∞, γ).
  Invariant vectors ξ_n give fixed isometries, and character vectors η_χ give eigen-isometries.
- **Item 2.** Embedding ⟹ [1] = 2[1]. And [1] = 0 ⟹ embedding by Cuntz comparison in the properly infinite F^α.
  The rest runs through Corollary 3.8 and §3.6.
- **Item 3.** For finite G, (A ⋊ G)_∞ = A_∞ ⋊ G, and the α̂-fixed central sequences are exactly the α-fixed central
  sequences of A.
- **Item 4.** w = v′v* is a fixed partial isometry, so φ_χ is well defined.
  - t_χ = |G|^{-1/2}Σ_g χ(g)s_g are orthogonal eigen-isometries with Σ_χ t_χt_χ* = F. So [F] = Σ_χ φ_χ[1].
  - F ~ 1 gives Rokhlin towers e_g = w*s_g s_g* w.

## 3.8 `o2-contractible-crossed-product-inner-half-flip-mcduff`: PASS

- **Item 1.** [ι_D] ∈ KK^G(C, D) ≅ K_0(O_2 ⋊_α G) = 0, so KK^G(j) = KK^G(k) = 0. Theorem 5.8 into (O_2 ⊗ O_2, α ⊗ α),
  which is outer, gives the approximately G-inner half-flip.
- **Item 2.** Szabó Proposition 3.3(ii) makes the infinite tensor power strongly self-absorbing.
  - The slice maps id ⊗ ω^{⊗∞} with an invariant state are admissible (Meyer--Nest Lemma 2.7).
  - In the Milnor sequence every connecting map is id ⊗ [ι_D] = 0, so the tensor power is contractible.
  - Contractible and outer gives Rokhlin (§3.6).
- **Item 3.** Rokhlin ⟹ McDuff through the model and Theorem 3.7. McDuff ⟹ absorption through the reindexation and
  Theorem 3.7 (iii) ⟹ (ii). Absorption ⟹ D ≃ D ⊗ 0 = 0 ⟹ Rokhlin.

## 3.9 `zp-detection-iff-bootstrap-sufficiency-and-kk-g-generation`: PASS, after the graph fix of §3.1

- **(L) ⟹ (D).** {X : KK^G(X, D) = 0} is localizing and contains Ind A and τA, by adjunctions.
- **(D) ⟹ (L).** Take the complementary pair of F = (Res, − ⋊ G), with left adjoint (A, B) ↦ Ind A ⊕ τB. The cellular
  approximation of a nuclear A is built from nuclear T^k(A), so N is nuclear and (D) kills it.
- **(S) ⟹ (D).** U(D) = Q(0, 0, K_*(D ⋊ G)) = 0 for D ∈ B^G with contractible restriction. Theorem 2.10 then gives
  KK^G(D, D) = 0.
- **(D) ⟹ (S).**
  - The Köhler lift has a nuclear cone D with U(D) = 0.
  - Res and − ⋊ G send the generators into B: Res C(G) = C^p, C ⋊ G = C^p, and C(G) ⋊ G = M_p. So Res D and D ⋊ G lie
    in B with zero K-theory.
  - Then (D) gives D ≃ 0.
- **(D) ⟹ (K).** Two contractible outer actions on O_2 ⊗ K: Corollary 6.4(i) lifts 0 to a conjugacy.
- **(K) ⟹ (D).** Compare with the Theorem 3.13 model of τO_2.

## Notes

- **Overlap.** `zp-detection-equals-meyer-nadareishvili-sufficiency` and this claim overlap on (S). Each node's
  `distinct_from` records it, so the duplication is declared, not hidden.
- **Novelty.** Both lanes claim no priority for the O_2 characterizations, and none was checked here.
