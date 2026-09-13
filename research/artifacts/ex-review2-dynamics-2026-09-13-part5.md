# EX review 2, dynamics: part 5. Remaining imports and the first-wave caveats

Lane `ex-verify2-dynamics`, tip `e55686d42f`. This part covers the claims that the first wave passed only with a
caveat, and the imports it checked without naming the node:
- ex-nonsofic-action-entropy (3ecde705af, d7a988a3fc, b7acd41a75);
- ex-rokhlin-lower (142d6e141e, aa3a1af8ca).

| claim | first-wave caveat | verdict |
|---|---|---|
| `popa-oe-superrigidity` (+ `-citation`) | source checked (§13e), id not named | PASS, verbatim (Theorems 0.3 and 0.4) |
| `alpeev-seward-stabilizer-growth-kills-outer-entropy` (+ `-citation`) | source checked (§13e), id not named | PASS, verbatim (Theorem 1.11) |
| `koopman-lambda-singular-part-has-zero-rokhlin-entropy`, consumed by `infinite-subgroup-invariant-information-has-zero-outer-entropy` | "given Seward Theorem 1.2" | PASS, verbatim, together with the outer-entropy convention |
| `sofic-free-actions-are-soe-invariant` (+ `-proof`) | "Step 3 of the amplification is a sketch" | PASS. The truncation step is written out below |
| `product-of-tree-groups-has-factorwise-howe-moore` (+ `-proof`) | Ciobotaru read only on pp. 1–5 and 13–17 | PASS. Every cited lemma was read, with its hypotheses |

## 5.1 Imports against the sources

- **Popa, arXiv:math/0512646v8.** Local `pdftotext`, lines 173–187.
  - **Theorem 0.3.** "Let Γ ↷σ X be as in 0.1. and assume in addition that Γ has no nontrivial finite normal
    subgroups and σ is free. [...] then n = t^−1 is an integer and there exist a subgroup Λ0 ⊂ Λ of index
    [Λ : Λ0] = n, a subset Y0 ⊂ Y of measure ν(Y0) = 1/n fixed by θ|Λ0, an inner automorphism α ∈ Inn(Rθ) and a
    group isomorphism δ : Γ ≃ Λ0 such that α∘∆ takes X onto Y0 and conjugates the actions σ, θ0∘δ".
  - **Theorem 0.4.** The opening matches the node verbatim.
  - **Theorem 0.1** was checked in part 3.
- **Alpeev–Seward, arXiv:1705.09707.** Local `pdftotext`, lines 305–316.
  - **Theorem 1.11.** "Let G ↷ (X, µ) be an aperiodic p.m.p. action. Consider a factor f. (i) If
    |Stab_G(f(x)) : Stab_G(x)| ≥ k for µ-almost-every x ∈ X then h^Rok_(G,µ)(Y, ν) ≤ (1/k)·h^Rok_G(Y, ν). (ii) If
    |Stab_G(f(x)) : Stab_G(x)| = ∞ for µ-almost-every x ∈ X then h^Rok_(G,µ)(Y, ν) = 0."
  - The extraction scrambles the fraction layout, but the reading is unambiguous. It matches the node.
- **Seward, arXiv:1804.05270.** Local `pdftotext`.
  - **Theorem 1.2** (lines 88–91). "Let G ↷ (X, µ) be a free p.m.p. action, and let ρ : G → U(L²_µ(X)) be the
    corresponding Koopman representation. [...] If H is a ρ(G)-invariant closed subspace of L²_µ(X) and ρ|H is
    singular with λ, then h_G(σ-alg(H)) = 0."
  - **Convention** (lines 25–35). "the (outer) Rokhlin entropy of ξ relative to F is defined to be
    h_G(ξ | F) = inf{H(α | F) : α a countable partition with ξ ⊆ σ-alg_G(α) ∨ F}".
  - So `h_G(σ-alg(H))` is the *outer* Rokhlin entropy of the invariant σ-algebra, which is what the zero outer
    entropy consumer uses.

## 5.2 `sofic-free-actions-are-soe-invariant`: PASS

**Amplification.**
- *The sheets.* Put `i(w) = min{i : k_i w ∈ V}`, which is finite almost everywhere because `V` meets almost every
  class.
  - `ι_n(w) = (k_(i(w)) w, i(w))` is injective on `P_n`: equal images force equal `i` and then `k_i w = k_i w'`.
  - It is measure preserving piecewise.
  - It carries `R|_(P_n)` onto `(R|_V × [n]^2)|_(ι_n(P_n))`, because `k_i w R w`.
- *Soficity of the truncation.* `[n]^2` is sofic (Cordeiro 3.5). The product is sofic (3.6), and so is its
  restriction (3.2(a)). These are verbatim in part 3.
- *Truncation.* Put `c_n(φ) = 1_(P_n) φ 1_(P_n)` and `δ_n = m(W ∖ P_n)`.
  - `c_n` changes `φ` only on `(W ∖ P_n) ∪ φ^(−1)(W ∖ P_n)`, of measure `<= 2δ_n`.
  - `c_n(φψ)` and `c_n(φ)c_n(ψ)` differ at most where `ψ` leaves `P_n` and `φ` brings it back, again of measure
    `<= 2δ_n`.
  - Traces move by at most `δ_n`. Normalizing on `P_n` adds `O(δ_n)`.
- *Composition.* Let `θ` be an almost morphism of `R|_(P_n)`, accurate on `c_n(F ∪ F·F)`. Then `θ∘c_n` is an
  `(F,ε)`-almost morphism of `R` once `δ_n < ε/20`.
  - The multiplicativity defect of `θ∘c_n` is at most `d(θ(c_n(φψ)), θ(c_nφ c_nψ)) + d(θ(c_nφ c_nψ), θ(c_nφ)θ(c_nψ))`.
  - Approximate isometry of `θ` bounds the first term by `2δ_n + o(1)`, and multiplicativity of `θ` bounds the
    second.
  - Approximate isometry holds because the distance on `[[R]]` is a fixed trace expression in domain idempotents
    and words of length `<= 4` (Cordeiro, sketch after Theorem 2.2, p. 3).
- **SOE chain.** The chain is Păunescu 1.15, then Cordeiro 3.2(a), then the isomorphism, then amplification, then
  1.15 again. All hypotheses hold for free actions.

## 5.3 `product-of-tree-groups-has-factorwise-howe-moore`: PASS

The lemmas are from Ciobotaru, arXiv:1403.0223v2, read in the local `pdftotext` extraction, lines 196–395 and
472–752.
- **Lemma 2.9.** It allows any decomposition `G = K_1AK_2` with compact `K_i` and an arbitrary subset `A`.
  - The product decomposition `(K_1×K_2)(A_1^+×A_2^+)(K_1'×K_2')` qualifies.
- **Lemma 4.7 and Example 4.10.** They give `G_i = Stab(x_0)A_i^+Stab(x_0)` for closed, strongly transitive,
  type-preserving `G_i`.
  - Example 4.10 records that, for a thick tree, strong transitivity is equivalent to 2-transitivity on the boundary
    (Caprace–Ciobotaru).
  - A topologically simple `G_i` is type-preserving: the type-preserving subgroup is open, normal and of index
    `<= 2`.
  - So the claim's class, closed, topologically simple and boundary-2-transitive on a bi-regular tree of valence
    `>= 3`, is exactly the tree case of Theorem 4.19.
- **Lemma 2.13.** Weak limits of pairwise commuting unitaries on a separable space are normal. Separability comes
  from Lemma 2.4.
- **Lemma 3.1, proof.** It shows `π(u_+)Eπ(u_−) = E`. Then `E(H)` is `U_α^+`-invariant, `E*(H)` is
  `U_α^−`-invariant, and `E*E = EE* != 0` gives a common nonzero vector.
  - The node uses the proof, not the statement, whose hypothesis `G = ⟨U_α^+, U_α^−⟩` fails for the product.
  - It concludes invariance under `G_1 × {e}` only, which contradicts the hypothesis. That adaptation is correct.
- **Escape.** For `g_n = (a_1^(m_n), a_2^(l_n))` with `m_n → ∞`, conjugation `g_n^(−1)(u,e)g_n = (a_1^(−m_n)ua_1^(m_n), e) → e`
  for `u ∈ U_(a_1)^+`. So `U_α^+ ⊇ U_(a_1)^+ × {e}`, and symmetrically for `U^−`.
- **Corollary 4.18.** It gives `⟨U_a^+, U_a^−⟩` normal in `G_1`.
  - It is nontrivial: for trees, `U_a^+` is the root group of the attracting end (Example 4.21).
  - So its closure is `G_1`, by topological simplicity.
- **The corollary for actions.** Ergodicity for `G_i` removes `G_i`-invariant vectors in `L²_0`. A sequence tending
  to infinity in a discrete subgroup tends to infinity in `G_1 × G_2`.
