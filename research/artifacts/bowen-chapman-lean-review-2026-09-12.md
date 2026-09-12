# Bowen–Chapman Problem 1.1 in Lean: independent review

Reviewer lane `bc-review`, 2026-09-12. This is one living file: every finding
names its evidence, the lane it was sent to, and its status. The target is an
unconditional Lean proof that some finitely generated group is surjunctive and
not sofic, with kernel closure exactly `[propext, Classical.choice, Quot.sound]`,
delivered through a Palomar challenge.

## F1. The Lean form of Kun–Thom Theorem 4.1 is stronger than the theorem

**Status: resolved in the plan, pending landing.** Sent to `kt-norm-paper`,
`kt-norm-repo`, `bc-assembly`, `bc-wreath`; the sequential free form below was
approved in reply to `kt-norm-repo`.

Kun–Thom, arXiv:2608.06222v3, Definition 2.1 (HTML, read 2026-09-12): "A
homomorphism σ:G→𝒮𝒰 is a *sofic representation* if tr(σ(g))=0 for every
g≠1." Theorem 4.1 is stated for sofic representations in this sense.

`HasSoficCentralizerNormalization Γ` (`Sofic/MFNonsoficDoubleEndpoint.lean`)
quantifies over every ultrafilter on ℕ, every family of finite models, and
every *injective* `ρ : G →* UniversalSofic 𝒰 X`.

* **Harmless cases.** Along a principal ultrafilter, or along models of bounded
  size, the ultraproduct is a finite symmetric group, so an infinite `G` admits
  no injective `ρ` and the condition is vacuous. A finite infranormal subgroup
  is normal (`isInfranormal_iff_normal_of_finite`), so finite `G` is harmless
  too.
* **The real gap.** Suppose `G` is sofic, as the explicit ambient group is,
  being residually finite. Take a free `σ` and an arbitrary homomorphism `τ`,
  amplified to models of equal size. Then `σ ⊕ τ` is injective, the Hamming
  length on the sum is the average of the two lengths, and centralizer elements
  `1 ⊕ q'` show that the Lean condition at `σ ⊕ τ` forces normalization for `τ`.
  So at a sofic group the landed Prop is equivalent to Theorem 4.1 for *every*
  homomorphism `G → 𝒮𝒰`, free or not. The paper proves the free case only.
* **What consumers need.** Kun–Thom use 4.1 only at `ρ|_G` for a sofic
  representation `ρ` of the wreath product (§5, proof of Theorem A: "choose a
  sofic representation ρ:Λ→S_U and write σ=ρ|_G"). In Lean,
  `not_isSofic_freeLamp_of_centralizerNormalization` builds its embedding from
  a `SoficApproximation`, whose field `asymptoticallyFaithful` says the Hamming
  length of `map n g` exceeds `1 − ε` eventually for `g ≠ 1`. The resulting
  embedding is free.

**Resolution.** `kt-norm-repo` proposed `HasSequentialCentralizerNormalization
Γ`. Its hypothesis is a `SoficApproximation G` and a sequence `v` whose
commutators with `A.map n γ` vanish along `atTop`, separately for each
`γ ∈ Γ`. Its conclusion is that the commutators of
`A.map n g * v n * (A.map n g)⁻¹` with `A.map n γ` vanish for all `g ∈ G` and
`γ ∈ Γ`. Reviewed and approved:

* **It follows from Theorem 4.1.** Suppose it fails on an infinite set `S`, and
  take a nonprincipal ultrafilter containing `S`. The approximation induces a
  homomorphism into the ultraproduct with trace zero off the identity (by
  `asymptoticallyFaithful`), that is, a sofic representation. The class of `v`
  lies in the centralizer of `Γ`, and 4.1 contradicts the failure on `S`.
  Uncountable groups admit no `SoficApproximation`, so there the Prop is
  vacuous, which is harmless.
* **It suffices for the endpoint.** Restricting a sofic approximation of the
  double or the wreath product along the injective inclusion of `G` keeps
  `asymptoticallyFaithful`. Taking `v n` to be the image of the lamp, separation
  on the nontrivial commutator gives the contradiction.
* **Follow-up.** The double reduction on main consumes the injective Prop, so a
  sequential reduction has to be added (`bc-assembly`, `bc-wreath`).

**Background read for this finding.**
* No sentence of Kun–Thom's Lemmas 2.3, 4.2 or 4.3 uses `tr(σ(g))=0`
  explicitly. The proof of Lemma 4.2 is "the construction of [1], Proposition
  3.3, Lemma 3.4, Definition 4.1 and Proposition 4.5, with the scale chosen
  diagonally", where [1] is V. Alekseev and A. Thom, *Centralizers of sofic
  approximations of Kazhdan groups*, arXiv:2608.05362 (5 August 2026).
* Alekseev–Thom's Definition 2.1 of a sofic approximation requires
  `d_H(θ_n(λ),1) → 1` for `λ ≠ e`. A summary of that paper says its sofic
  embeddings carry no trace condition. This was not checked against the text,
  and the endpoint does not depend on it.
* The Cairn claim `rigid-compression-defect-normalization-dichotomy` asserts
  that normalization for trace-preserving representations implies it for every
  homomorphism. That would make the injective Prop true as well. It is not
  formalized, and the endpoint does not need it.

## F2. Statement fidelity of the challenge

**(a) Printed setting. Status: sent to `bc-palomar`.** Bowen–Chapman,
arXiv:2511.06586v1, §1: "Let Γ be a finitely generated group, Σ a finite set
(of colors), and Σ^Γ the Σ-colorings of Γ." Problem 1.1 is posed in that
setting, so `exists_finitelyGenerated_surjunctive_not_sofic` is the literal
negative answer. `not_all_surjunctive_groups_sofic` is equivalent, because
soficity is determined by finitely generated subgroups and surjunctivity passes
to subgroups, but the docstring should present the finitely generated theorem
as the printed one.

**(b) Direction of the sofic bridge. Status: sent to `bc-palomar`.** The
challenge concludes `¬ IsSoficGroup`, so the solution needs
`IsSoficGroup G → IsSofic G`. The non-MF `Palomar/Solution.lean` only exhibits
models, which is the other direction. The needed direction is a transcription:
`SoficModel` has the same three fields, and `hammingDistance` is the
disagreement count divided by the cardinality, as `hammingDist` is.

**(c) Automaton convention. No defect.** Bowen–Chapman:
`Φ(c)(x)=ϕ(c(xγ₁),…,c(xγₙ))`. Challenge: `fun c x => φ fun i => c (x * γ i)`.
These are identical, and such maps commute with left translation.

**(d) Degenerate cases. No defect.**
* Empty palette: `G → A` is empty, and both conditions hold vacuously.
* `n = 0`: the automaton is constant. It is injective only for a subsingleton
  palette, and then it is surjective.
* Repeated `γ_i` are allowed, so the class is all cellular automata.
* Quantifying over finite palettes in `Type` loses nothing.
* Model tests: finite groups are surjunctive (an injective self-map of a finite
  set is onto), and ℤ is residually finite, hence surjunctive.
* `IsSoficGroup` is not vacuous: one-point models fail separation for `ε < 1`,
  and finite groups pass through the left regular action.

**(e) The development's notion implies the challenge's. No defect.**
`Surjunctivity.IsSurjunctive` asks every continuous, shift-equivariant,
injective map over every finite discrete palette to be surjective, where
`shift k x g = x (k * g)`. With `M` the image of `γ` and
`μ y = φ (fun i => y ⟨γ i, _⟩)`, `localMap M μ` equals the challenge automaton,
and it is continuous and equivariant (`continuous_localMap`,
`localMap_isEquivariant`), so `IsSurjunctive.surjective_localMap` applies.

## F3. The mathematics in the lane briefs

**(a) `bc-pair`, infranormality and non-normality. No defect.**
* The compression direction matches `compressionSubmonoid` (`g * γ * g⁻¹ ∈ Γ`),
  since `inr M · inl A · (inr M)⁻¹ = inl (φ_M A)`.
* On the `(i,j)` block, `e_ij(1)·e_ji(−1)·e_ij(1) = [[0,1],[−1,0]]`, whose
  square is `diag(−1,−1)`. So `D₁ = diag(−1,−1,1)` and `D₂ = diag(1,−1,−1)` lie
  in `EL₃(ℤ)`.
* `v = v⁺ + D₁(a⁻,b⁻,0) + D₂(0,0,c⁻)`.
* The commutator through the third index gives `T + T ⊆ T`.
* Non-normality: column 1 of `e_01(−1)` is `(−1,1,0)`, and the entries of
  elements of the peripheral subgroup lie in the range of `polyToLaurent`,
  whose supports lie in the image of ℕ³.

**(b) `bc-rf`, residual finiteness. Status: gap sent to `bc-rf`, fix proposed.**
The action on `V_n = (R_n)³` is a genuine left action: the product is
`(A,M)(B,N) = (A·φ_M(B), MN)`, reduction mod `n` commutes with substitution, and
`σ̄_M` is a ring hom.

The briefed separation for `M ≠ 1` is incomplete. `(A,M)` sends `x^(e_j)·e_k`
to `x^(M̄e_j)·col_k(Ā)`, and a monomial-diagonal `Ā` can make this equal
`x^(e_j)·e_k`, so the support comparison can fail. The fix uses two tests:
* if `ψ_n(A,M) = 1`, testing `e_k` forces `Ā = I`, and then `M̄ = I`;
* choose `n` exceeding both `max|M_ij − δ_ij|` and twice the largest absolute
  exponent in the entries of `A − 1`.

**(c) `bc-kazhdan`, semidirect (T). Status: wording note sent, no defect in the
argument.** The sketch said "some q moves every vector of `H^N⊥`". The repo's
`IsKazhdanPair` only gives a moving `q` for each vector separately, applied to
the restriction on the closed subspace `H^N⊥`. The needed estimate
`‖ξ − Pξ‖ ≤ δ/ε_N` still follows per vector.

**(d) `bc-double-surj`, finitary site for doubles. No defect.**
* `α` is an action: `α_g α_h e_x = e_(ghx)·e_(ghx₀)⁻¹`.
* Checked against every field of `Dynamics/FinitarySite.lean`:
  * surjectivity of the projections; residual finiteness (free groups);
  * `A ∅` is trivial;
  * coherent injective embeddings;
  * detection by the union of letters;
  * `support n = letters(n) ∪ {x₀}`, with `finiteSupport` because the letters
    of `α_g n` lie in `g·support n`;
  * `stabilizer_invariance`, in both cases `x₀ ∈ S` and `x₀ ∉ S`. If `k` fixes
    `S` pointwise and `x ∉ S`, then `kx ∉ S`, because `k⁻¹` also fixes `S`
    pointwise.

**(e) `bc-wreath`, nonsoficity of the wreath product. No defect.**
* The lamp at `x₀` commutes with `Γ`.
* Normalization at `t` makes the lamp at `t·x₀` commute with `γ`, and
  faithfulness forces `γ·t·x₀ = t·x₀`, i.e. `t⁻¹γt ∈ Γ`.
* This matches Kun–Thom §5. The representation it uses comes from a sofic
  approximation, so it is free, which fits F1.

## F4. Landed code

As of `origin/main` 8a1a183c9, only WIP snapshots under `wip/bowen-chapman/`
exist: the Dynamics library and the endpoint scaffolds. No campaign module has
landed at its final path. Lanes still to review as they land: `bc-pair`,
`bc-kazhdan`, `bc-rf`, `bc-dynamics` / `bc-dynamics-upper`, `bc-double-surj`,
`bc-wreath`, `kt-norm-paper`, `kt-norm-repo`, `kt-norm-fixedpoint`,
`kt-norm-counting`, `bc-assembly`, `bc-palomar`.

An informal pass of the permanence chain by another team is not a Lean
verification; the Lean is reviewed here independently.

## Credit and priority

* **The question.** Bowen and Chapman (arXiv:2511.06586v1, submitted 10 November
  2025) pose Problem 1.1 as "another natural problem that arises from" the work
  of Gromov and Weiss, their references [14] and [26], and cite no earlier
  statement of it. A web search for earlier printed statements of the converse
  question found nothing earlier.
* **Earlier examples.** Two web searches on 2026-09-12 found no earlier
  surjunctive nonsofic group. The hits were the Bowen–Chapman paper,
  Fournier-Facio's torsion-free nonsofic group (arXiv:2608.02025), and papers
  on surjunctivity for monoids and non-uniform automata. This is a bounded
  check, not an exhaustive one.
* **The mechanism.** Nonsoficity of the witness comes from Kun–Thom,
  arXiv:2608.06222v3, Theorem A. Their Lemma 4.2 rests on Alekseev–Thom,
  arXiv:2608.05362. Both are to be proved in Lean, not cited.
