# The topological full group inside G_X, part 2: firewall, other subgroups, prior art, model tests

Lane `sk-subgroups` (SK swarm), 2026-09-13. Written proofs, UNREVIEWED (queued with sk-referee-2). Notation as in part 1.

## 4. Firewall: the Whitehead diagonal map is a homomorphism only on commuting units
**Claim W.** Let `R` be a unital ring and `a, b ∈ R^×`. Then `diag(a,a^{-1},1)·diag(b,b^{-1},1) = diag(ab,(ab)^{-1},1)` if and only if `ab = ba`. So for an injective homomorphism `θ : Γ → R^×`, the map `ι(g) = diag(θ(g), θ(g)^{-1}, 1)` is a homomorphism if and only if `Γ` is abelian.

*Proof.* The second slot of the product is `a^{-1}b^{-1} = (ba)^{-1}`, and it equals `(ab)^{-1}` iff `ab = ba`. ∎

**Witness inside `[[T]]` for every infinite minimal Cantor system.**
- Choose a clopen `U` with `U, TU, T²U` disjoint.
- `σ = T` on `U`, `T^{-1}` on `TU`, and the identity elsewhere.
- `τ = T` on `TU`, `T^{-1}` on `T²U`, and the identity elsewhere.
- Then `στ(U) = TU` but `τσ(U) = T²U`, so `στ ≠ τσ`. By part 1 Lemma 1, `w_σ w_τ ≠ w_τ w_σ`, and `ι(σ)ι(τ) ≠ ι(στ)`.

**Impact on main (reported to main 2026-09-13).**
- `crossed-product-group-embeds-in-projective-elementary-group` asserts that `ι` is an injective homomorphism `Γ → EL_N(R)` for every `Γ`, and its route `crossed-product-group-projective-elementary-embedding-proof` says in step 2 "ι is a homomorphism". This is false for nonabelian `Γ`.
- The review (un-review3 part 3 §7) checked Whitehead's identity and the centre, not multiplicativity.
- Consumers, which apply it to the nonabelian Abels–Prüfer group `Γ_p` for every `N ≥ 3`:
  - `simple-kazhdan-linear-sofic-non-lef-via-abels-prufer-subflow`, which feeds `simple-kazhdan-linear-sofic-non-lef-group-exists`;
  - `rank-modelled-non-lef-el-via-amenable-non-rf-subflow`, which feeds `rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group`.
- The note is unaffected: for `Γ = Z` the map is correct.

**Correct replacements.**
1. *Derived subgroup.* `g ↦ diag(θ(g),1,1)` is a homomorphism. On `[Γ,Γ]` it lands in `EL_3(R)`, because `diag(aba^{-1}b^{-1},1,1) = diag(a,a^{-1},1)·diag(b,b^{-1},1)·diag((ba)^{-1},ba,1)`.
2. *Slotwise cancellation.*
   - Suppose `Γ = ⟨S⟩` and `ψ : Γ → R^×` is a homomorphism with `ψ(s) = θ(s)^{-1}` for `s ∈ S`, e.g. `ψ = θ∘α` for an automorphism `α` inverting `S`, as for free groups and `Z^d`.
   - Then `diag(θ(g), ψ(g), 1)` is a homomorphism whose generators are Whitehead matrices, so its image lies in `EL_3(R)`.
   - For `Z`: `ψ(n) = u^{-n}`. For `[[T]]` over `F_2`: `ψ = u^{-I}`, where the finite-order generators are handled by tower permutations (part 1, Theorem B).
3. *Through the ring, for the non-LEF consumers.*
   - For `N ≥ 4`, `lef-el-groups-force-exactly-matricial-simple-ring` gives: `EL_N(R)` LEF ⇒ `R` is a LEF ring ⇒ `R^×` is LEF, since partial ring models restrict to injective partial group models on units and their inverses.
   - `R^× ⊇ θ(Γ_p)` is not LEF, so `EL_N(R)` is not LEF for `N ≥ 4`.
   - Rank `N = 3` stays uncovered by this repair.

**Landed repair (2026-09-13).**
- The firewall is the existing `whitehead-diagonal-map-is-not-multiplicative` (bh-reviewer, 2026-09-12). Its
  `invalidates:` now also lists:
  - `crossed-product-group-projective-elementary-embedding-proof`;
  - `simple-kazhdan-linear-sofic-non-lef-via-abels-prufer-subflow`;
  - `rank-modelled-non-lef-el-via-amenable-non-rf-subflow`.
- `crossed-product-group-embeds-in-projective-elementary-group` is restated (abelian images; derived subgroup) and left open, with Attempts.
- Repaired routes, both for `N >= 4`:
  - `simple-kazhdan-linear-sofic-non-lef-via-lef-converse`, for `S_N = EL_N(R)` when `q = 2`;
  - `rank-modelled-non-lef-el-via-lef-converse`, for `EL_4(R)`.

## 5. Other subgroups (proofs short; unreviewed)
- **Every finite group.**
  - `T` has no periodic points, so towers of every height `h` exist.
  - The map `Φ : GL_{3h}(F_2) → G` of part 1 Lemma 3 is injective, because the matrix units `E_ab E_pq` are linearly independent.
  - `GL_{3h}(F_2) ⊇ Sym(3h)` contains every group of order at most `3h`.
- **A Kazhdan S-arithmetic lattice and free subgroups.**
  - `F_2[u^{±1}] ⊆ R` (unique representation), and `F_2[t^{±1}]` is Euclidean, so `SL_3(F_2[t^{±1}]) = E_3(F_2[t^{±1}])` embeds in `G_X` with `t ↦ u`.
  - It contains nonabelian free subgroups, e.g. in `SL_2(F_2[t])`.
- **Factors.** If `X → X'` is a factor map onto an infinite minimal subshift, then `LC(X',F_2) ⊆ LC(X,F_2)` equivariantly and `u ↦ u`. So `R_{X'} ⊆ R_X` unitally, and `G_{X'} ⊆ G_X`.
- **Not linear.** `G_X` is finitely generated, infinite and simple, so it is not residually finite and hence not linear (Mal'cev).
- **Induced systems (sketch, OPEN as a node).**
  - For a clopen `U ≠ ∅`, the corner `e_U R e_U` should be `LC(U,F_2) ⋊_{T_U} Z` for the first-return map `T_U`, with `v = Σ_r u^r e_{U_r}`.
  - Then `A ↦ (1−e_U)I_3 + A` embeds `EL_3(e_U R e_U)` in `G_X`, so `G_{X_U} ⊆ G_X` for every induced subshift `X_U`.
  - The corner isomorphism (surjectivity via return counts, injectivity via distinct displacements) is standard but not written out here.

## 6. Prior art and novelty (bounded)
Search bound: a Cairn grep on main for full groups, Whitehead, Juschenko, Matui and elementary groups, plus the two sources, read in full where cited.
- **Full-group units.** Main already has `full-group-units-embed-in-steinberg-algebras` (the bisection units `1_U`). In C*-algebras this is standard: `[[φ]]` sits in the unitary normalizer of `C(X)` in `C(X) ⋊ Z` (Giordano–Putnam–Skau). Part 1 Lemma 1 is the `Z`-crossed-product instance, written in the note's conventions.
- **Whitehead's lemma.** Standard algebraic K-theory.
- **Properties of `[[T]]'`.** Matui (simple; f.g. iff subshift) and Juschenko–Monod (amenable), both quoted in part 1 from the arXiv PDFs. Journal data verified through Crossref:
  - Matui, Internat. J. Math. 17(2) (2006) 231–251, doi:10.1142/S0129167X06003448;
  - Juschenko–Monod, Ann. of Math. 178(2) (2013) 775–787, doi:10.4007/annals.2013.178.2.7.
- **Novelty.**
  - Corollary A is routine given the imports. Its value is the juxtaposition: an infinite f.g. simple amenable group inside an infinite f.g. simple Kazhdan LEF group, from one subshift. I located no published statement of it.
  - Theorem B (all of `[[T]]`) needs the flux and Kakutani–Rokhlin argument of part 1 and may be new in this form. It is folklore-level.
  - Claim W is elementary. It matters because main has a reviewed node that misses it.

## 7. Model tests
- **Hypotheses bind (periodic `X`).** For a finite orbit `X = Z/p` the cocycle `n_g` is not unique, so `g ↦ w_g` is not well defined. Towers taller than `p` do not exist, so Lemma 4 fails. Theorem B's hypotheses are genuinely used.
- **The note's example.** For the Fibonacci subshift all hypotheses hold (infinite, minimal, subshift), and `[[T]]'` is finitely generated (Matui 5.4).
- **Coefficients.** Over `F_q` with `q` odd, a level transposition has determinant `−1` in `GL_{3h}(F_q)`, so Lemma 3 fails for odd permutations and Theorem B's proof does not transfer. Corollary A holds over every field through the signed Whitehead identity.
- **Firewall calibration.** Abelian `Γ = Z` passes Claim W, which is the note's `diag(u,u^{-1},1)`. The two level swaps `σ, τ` fail it.
