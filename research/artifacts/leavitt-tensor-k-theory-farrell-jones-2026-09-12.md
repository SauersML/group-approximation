# K-theory of Leavitt tensor powers through the Farrell–Jones conjecture

Lane `bh-leavitt-nil-k-regularity`, 2026-09-12. The crossed-product
decomposition is by lane `bh-coherence-kumjian-pask`, in
`research/artifacts/leavitt-tensor-crossed-product-2026-09-12.md`.

## 1. Result

**Theorem.** For every field `k` and every `d >= 1`,
`K_n(L_k(1,2)^(⊗d)) = 0` for every `n ∈ Z`, in non-connective algebraic
`K`-theory.

It is node `leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees`, with
route `leavitt-tensor-powers-k-vanishing-via-farrell-jones-proof`. It feeds
`leavitt-tensor-powers-have-trivial-k-theory` over `F_2` and
`prime-field-leavitt-tensor-powers-have-trivial-k-theory` over every `F_p`,
through the two specialization routes `…-via-all-degree-vanishing`.

**Why the coherence obstruction does not matter.**
`leavitt-tensor-powers-are-not-left-coherent` kills the inductive route through
`L^(⊗(d−1))`. The Farrell–Jones conjecture for `Z^(d−1)` bypasses every
intermediate ring: it computes `K(C ∗ Z^(d−1))` from the crossed products over
virtually cyclic subgroups. Those are `C` and skew Laurent rings `C_φ[t, t^−1]`
over the semihereditary, `K`-trivial ring `C = L_0^(⊗(d−1)) ⊗ L`.

## 2. Sources, read from arXiv e-print TeX on MSI

All four were fetched with `curl https://arxiv.org/e-print/<id>` into
`/scratch.global/sauer354/nilk/src/` and read as TeX.

### 2.1 Bartels–Farrell–Lück, arXiv:1101.0469

- **Theorem "Virtually poly-Z-groups"** (`the:FJC_virtually_poly_Z-groups`):
  "Let G be a virtually poly-Z-group (see Definition def:virtually_poly-Z). Then
  both the K-theoretic and the L-theoretic Farrell-Jones Conjecture with additive
  categories as coefficients with respect to the family VCyc (see
  Definition def:K-theoretic_Farrell-Jones_Conjecture and
  def:L-theoretic_Farrell-Jones_Conjecture) hold for G."
- **Definition `def:K-theoretic_Farrell-Jones_Conjecture`:** "G satisfies the
  K-theoretic Farrell-Jones Conjecture with additive categories as coefficients
  with respect to F if for any additive G-category A the assembly map
  asmb^{G,A}_n : H_n^G(E_F G; K_A) → H_n^G(pt; K_A) = K_n(∫_G A) induced by the
  projection E_F G → pt is bijective for all n ∈ Z."
- **Remark "Relevance of the additive categories as coefficients":** "The
  versions of the Farrell-Jones Conjecture appearing in Definition ... are
  formulated and analyzed in [Bartels-Lueck(2009coeff)],
  [Bartels-Reich(2007coeff)]. They encompass the versions for group rings RG
  over arbitrary rings R, where one can built in a twisting into the group ring
  or treat more generally crossed product rings R ∗ G".

**Not enough: Bartels–Lück, arXiv:0901.0442.** Their CAT(0) result gives the
`K`-theoretic assembly map only "bijective in degree m ≤ 0 and surjective in
degree m = 1". That misses `K_2`, so the all-degree theorem above is the one used.

### 2.2 Bartels–Reich, arXiv:math/0510602

- **Section "Crossed products":** "Let R be a ring, G be a group and α: G → Aut(R),
  g ↦ α_g and τ: G × G → R^×, (g,h) ↦ τ_{g,h} be maps. We require that
  τ_{g,h} τ_{gh,k} = α_g(τ_{h,k}) τ_{g,hk} and
  τ_{g,h} α_{gh}(r) = (α_g ∘ α_h)(r) τ_{g,h} ... We will also assume that
  α_e = id_R ... (rg)·_{α,τ}(sh) = r α_g(s) τ_{g,h} gh."
- **Corollary `cor:crossed-product-in-category-language`:** "Suppose we are given
  a crossed product situation R, α: G → Aut(R), τ: G × G → R^×. Then there exists
  an additive category A_{α,τ} with a right G-action, such that for every orbit
  G/H the category A_{α,τ} ∗_G G/H and the category F^f(R_{α|,τ|}H) of finitely
  generated R_{α|,τ|}H-modules are equivalent. ... In particular there is for
  every G/H and every n ∈ Z an isomorphism
  K_n(A_{α,τ} ∗_G G/H) ≅ K_n(R_{α|,τ|}H)."
- **Conjecture `con:FJ-for-crossed-product`:** "Suppose R_{α,τ}G is a crossed
  product ring, then the assembly map
  H^G_*(E_VCyc G; K_{A_{α,τ}}) → H^G_*(pt; K_{A_{α,τ}}) ≅ K_*(R_{α,τ}G) induced
  from E_VCyc G → pt is an isomorphism." It is called a special case of the
  conjecture with coefficients.

### 2.3 Bartels–Lück, arXiv:2002.03412

The arXiv abstract page gives the journal reference Proc. Roy. Soc. Edinburgh
Sect. A 154 (2024) 1945–2023.

- **Definition of regularity for rings.** "We call R regular coherent, if every
  finitely presented R-module M is of type FP"; "l-uniformly regular coherent, if
  every finitely presented R-module M admits an l-dimensional finite projective
  resolution".
- **The Laurent categories.** "define A[Z^m] inductively over m by
  A[Z^m] := A[Z^{m−1}]_id[t,t^{−1}], where A[Z^{m−1}]_id[t,t^{−1}] is the
  (untwisted) finite Laurent category".
- **Theorem `the:The_non_connective_K-theory_of_additive_categories`:** "Let A be
  an additive category. Suppose that A[Z^m] is regular coherent for every m ≥ 0.
  Consider any automorphism Φ: A → A of additive categories. Then we get a weak
  homotopy equivalence of non-connective spectra
  a^∞ : T_{K^∞(Φ^{−1})} → K^∞(A_Φ[t,t^{−1}])." The proof records
  "π_n(NK^∞(R_Φ[t])) = π_n(NK^∞(A_Φ[t^{−1}])) = 0 for all n ∈ Z".
- **Corollary `cor:regualiyt_for_R-versus_underline(r)_oplus)`:** "The ring R is
  ... regular coherent ... [iff] the additive category R_⊕ is ... regular
  coherent ...".

### 2.4 Lück–Steimle, arXiv:1309.1353

- **Main theorem** (non-connective twisted BHS): "There exists a weak homotopy
  equivalence of spectra, natural in (A,Φ),
  T_{K^∞(Φ^{−1})} ∨ NK^∞(A_Φ[t]) ∨ NK^∞(A_Φ[t^{−1}]) → K^∞(A_Φ[t,t^{−1}])".
- **Example "Finitely generated free R-modules":** "If R comes with a ring
  automorphism φ ... then R_Φ[t,t^{−1}] is equivalent to the category of finitely
  generated free modules over the twisted group ring R_φ[t,t^{−1}]."
- **Theorem `the:Passage_to_the_idempotent_completion`, part 2:** "The map of
  non-connective spectra K^∞(η(A)) : K^∞(A) → K^∞(Idem(A)) is a weak homotopy
  equivalence."

## 3. Proof outline

The full text is route `leavitt-tensor-powers-k-vanishing-via-farrell-jones-proof`.

1. **The crossed product.** `L^(⊗d) = C_(α,τ)Λ` with `Λ ≅ Z^(d−1)`,
   `ū_λ = u^λ`, `α_λ = Ad(u^λ)` and `τ_(λ,μ) = u^λ u^μ (u^(λ+μ))^(−1) ∈ C^x`.
2. **Assembly.** By 2.2 and 2.1, `H_n^Λ(E_VCyc Λ; K_A) ≅ K_n(L^(⊗d))` for every
   `n`.
3. **Orbit values.**
   - `H = 1` gives `K(C) ≃ 0`.
   - `H = Zλ` gives the skew Laurent ring `C_φ[t, t^−1]`, with `t = u^λ`.
     - Every `C[Z^m]` is regular coherent. It is a central localization of the
       regular coherent `C[t_1, ..., t_m]`, and the side does not matter, through
       the anti-automorphism `x_i ↦ y_i`.
     - So by 2.3 and 2.4, `K(C_φ[t, t^−1]) ≃ T_(K(φ^−1)) ≃ 0`.
4. **The source vanishes.** A `Λ`-homology theory whose values vanish on every
   orbit type of the `Λ`-CW-complex `E_VCyc Λ` vanishes on it, by induction on
   skeleta and passage to the colimit. These are standard properties of
   `Or(G)`-spectrum homology theories (Davis–Lück). They were not re-read here.
5. **Conclusion.** `K_n(L^(⊗d)) = 0` for every `n`.

## 4. Remark: K-regularity comes for free

The same argument, with `C[s_1, ..., s_p]` in place of `C`, gives
`K(L^(⊗d)[s_1, ..., s_p]) ≃ 0` for every `p`.
- `L^(⊗d)[s] = C[s] ∗ Λ`, with the same units, since the variables `s_i` are
  central.
- `K(C[s]) = colim K(M_N(L[s])) = colim K(L_2 ⊗ k[s]) = 0`, by Ara–Cortiñas
  Proposition 6.2 with `R = k[s]`, which is regular Noetherian and so regular
  supercoherent.
- `C[s][Z^m]` is regular coherent, by the same localization step.

So `L^(⊗d)` is `K`-regular and `K = KH = 0`. This is consistent with ABC Theorem
8.6. This remark is **not wired** as a node.

## 5. What was not checked

- The journal references of Bartels–Farrell–Lück, Bartels–Reich and Lück–Steimle;
  only the arXiv sources were read.
- The Davis–Lück properties used in Step 4.
- The symbol-level match of `∫_G A` (Bartels–Farrell–Lück) with `A ∗_G pt`
  (Bartels–Reich). The Bartels–Farrell–Lück remark quoted in 2.1 places their
  definition in the Bartels–Lück and Bartels–Reich framework, and says it covers
  crossed product rings `R ∗ G`, but the definition of `∫_G A` was not read.
- The downstream Boone–Higman chain: `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`,
  `khanh-acyclicity-and-steinberg-criteria` and the embedding claim. This lane
  did not re-verify them. They rest on imports that include Khanh's unrefereed
  preprint.
- Novelty: none claimed. The argument is a standard application of the
  Farrell–Jones conjecture with coefficients, and none of the sources read state
  the result for `d >= 3`.
- Review: not independently reviewed at the time of writing.
