# Bowen–Chapman Problem 1.1 in Lean: independent review

Reviewer lane `bc-review`, 2026-09-12. This is one living file: every finding
names its evidence, the lane it was sent to, and its status. The target is an
unconditional Lean proof that some finitely generated group is surjunctive and
not sofic, with kernel closure exactly `[propext, Classical.choice, Quot.sound]`,
delivered through a Palomar challenge.

## F1. The Lean form of Kun–Thom Theorem 4.1 is stronger than the theorem

**Status: resolved in the plan, pending landing.** Sent to `kt-norm-paper`,
`kt-norm-repo`, `bc-assembly`, `bc-wreath`; the sequential free form below was
approved in reply to `kt-norm-repo`, and `kt-norm-paper` confirmed that all four
Theorem 4.1 lanes now target it.

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
  Uncountable groups have no `SoficApproximation`, so there the Prop is
  vacuous, which is harmless.
* **It suffices for the endpoint.** Restricting a sofic approximation of the
  double or the wreath product along the injective inclusion of `G` keeps
  `asymptoticallyFaithful`. Taking `v n` to be the image of the lamp, separation
  on the nontrivial commutator gives the contradiction.
* **Follow-up.** The double reduction on main consumes the injective Prop, so a
  sequential reduction has to be added. `kt-norm-repo` owns
  `not_isSofic_symmetricDouble_of_sequentialNormalization`.

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

**(a) Printed setting. Status: fixed by `bc-palomar` at 6ae077316, verified.**
Bowen–Chapman, arXiv:2511.06586v1, §1: "Let Γ be a finitely generated group, Σ a
finite set (of colors), and Σ^Γ the Σ-colorings of Γ." Problem 1.1 is posed in
that setting, so `exists_finitelyGenerated_surjunctive_not_sofic` is the literal
negative answer. `not_all_surjunctive_groups_sofic` is equivalent, because
soficity is determined by finitely generated subgroups and surjunctivity passes
to subgroups. The landed challenge header now says both things.

**(b) Direction of the sofic bridge. Status: fixed in the WIP solution draft,
verified at origin/main 0c56757f9.** The challenge concludes `¬ IsSoficGroup`,
so the solution needs `IsSoficGroup G → IsSofic G`. The non-MF
`Palomar/Solution.lean` only exhibits models, which is the other direction. The
draft now has `isSofic_of_isSoficGroup` and `isSoficGroup_iff_isSofic`, a
transcription through `SoficModel`. It relies on `hammingDist` and
`hammingDistance` agreeing definitionally, and it is not yet compiled.

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
`localMap_isEquivariant`), so `IsSurjunctive.surjective_localMap` applies. The
WIP solution's `isSurjunctive_of_surjunctive` does exactly this. Its equation
`localMap M μ = cellularAutomaton γ φ` holds by `rfl`, since both sides reduce to
`fun c x => φ fun i => c (x * γ i)`.

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

**(b) `bc-rf`, residual finiteness. Status: gap sent to `bc-rf`; fixed at
dfa8d5e7b, verified (F4(h)).**
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

## F4. Landed code and early drafts

As of `origin/main` 73f646f13 fourteen landings touch the campaign: the Palomar
challenge (6ae077316), solution (1ad7aa663) and pending gate registration
(73f646f13), the Dynamics base layer (5e2c62ed1), the site-strata leaves
(0bfc073cd), semidirect (T) (3d4569114), the Laurent pair (031156388), residual
finiteness (dfa8d5e7b), the coset wreath algebra (2d5427380), the Dynamics upper
layer (684f9d301), residual finiteness of the ambient group (e728fe4e7),
surjunctivity of symmetric doubles (53d1db321), infranormality and
non-normality (8d36818d4), and property (T), finite generation and countability
(3e8c96515). Everything else is a WIP snapshot under `wip/bowen-chapman/`.

**Stale oleans.** The shared MSI checkout's oleans were built at a7bf5d4fc
(30 August). A private-directory green counts only if every repository
dependency's olean was built from source byte-identical to main.
`lake-manifest.json` and `lean-toolchain` are unchanged since a7bf5d4fc, so
Mathlib-only builds are not exposed.

**(a) Endpoint scaffolds, WIP at cdd4b82df. Status: fixed by `bc-assembly` at
958615284 (WIP snapshots).** Verified by reading both snapshots on origin/main
2648d3624: they import `KunThom.NormalizationFromCriterionConsumer`, use
`HasSequentialCentralizerNormalization`,
`hasSequentialCentralizerNormalization_of_kazhdan_infranormal` and
`not_isSofic_symmetricDouble_of_sequentialNormalization`, and no longer mention
the injective Prop. The header now attributes the sequential form to Kun–Thom
Theorem 4.1. The original findings were:
* The statements of `symmetricDouble_fg_surjunctive_not_isSofic` and
  `exists_fg_surjunctive_not_isSofic` match the pinned interface.
* The Theorem 4.1 input was the injective `HasSoficCentralizerNormalization`,
  which no lane will prove after F1.
* The header of `EndpointOfInputs` ascribed the faithful-representation form to
  Kun–Thom Theorem 4.1. The theorem is for sofic representations.
* The surjunctivity and finite-generation calls agree with the Dynamics
  signatures: `symmetricDouble_finitelyGenerated (G) [Group.FG G] (Γ)` and
  `isSurjunctive_of_residuallyFinite [Group.ResiduallyFinite G]`.

**(b) Local drafts read early: unlanded and unbuilt, so these are notes, not
verdicts.**
* **`BowenChapman/LaurentPair.lean` (`bc-pair`).** Matches the pinned
  definitions:
  * `substitution M` is `mapDomainRingEquiv` along `v ↦ M *ᵥ v`, and it is
    covariant (`exponentAction_mul`);
  * `actorAction` acts entrywise;
  * `Peripheral` is the range of `inl ∘ elementaryGroupMap polyToLaurent`.
  The Mathlib names check at 81a5d257: `mapDomainRingEquiv_single` takes the
  equivalence, then the coefficient, then the exponent, as the draft calls it.
  The docstring's "SL₃(ℤ) replaced by EL₃(ℤ), the same group" is true, and it
  is used only as prose.
* **`BowenChapman/LaurentPairKazhdan.lean` (`bc-kazhdan`).** It calls
  `peripheralEmbedding_injective`, which does not exist; LaurentPair defines
  `peripheralHom_injective`. Sent, and fixed in the WIP snapshot, which now uses
  `MonoidHom.ofInjective peripheralHom_injective`. The (T) inputs are sound:
  * `finitelyGeneratedRingGeneralRankElementaryPropertyT` is root-imported at
    7db678817, carries a closed-axioms audit line in
    `PropertyT/IntegralColumnPlaneClosure.lean`, and covers every finitely
    generated unital ring in `Type`, including ℤ, `Laurent` and `Poly`;
  * `AddMonoidAlgebra.finiteType_of_fg` exists at the pin with explicit ring and
    monoid, and the `AddMonoid.FG` instances for ℕ, ℤ and finite products exist,
    so the finite-type route resolves.
* **`Kazhdan/SemidirectProductKazhdan.lean` (`bc-kazhdan`).** The statement
  matches the pinned permanence theorem. The proof goes through a per-vector
  moving-projection estimate, as F3(c) requires.
* **`Sofic/WreathCentralizerNormalization.lean` (`bc-wreath`).** The algebraic
  core `wreath_conj_mem_of_commute` involves no representation, so swapping in
  the sequential Prop only touches the consumer.

**(c) Landed: `Palomar/BowenChapmanChallenge.lean`, 6ae077316. Content: no
defect. Evidence: flagged, then closed by `bc-palomar` at 1ad7aa663, verified.**
1ad7aa663 lands the solution, the configuration, the three drivers and the
`PalomarBowenChapmanSolution` library. Its message records a private MSI build
with Lean 4.32.0 and the md5 checked in the same invocation, exit 0 for the
challenge (only the hole warnings), for the solution under
`-DwarningAsError=true`, and for the development closure (`Sofic/Asymptotics`,
`Sofic/Sofic`, `Dynamics/Surjunctivity`) compiled from main's blobs. All eight
quoted md5s equal the blobs of that commit. The solution library is not a
default target. The solution still has only the `_of` forms while the
configuration names the unsuffixed theorems, so the configuration is correctly
pending and no gate or workflow mentions it yet. The earlier notes on 6ae077316
were:
* Imports are Mathlib only. The header quotes Problem 1.1 verbatim, states the
  finitely generated setting, claims nothing beyond the two compared theorems,
  and discloses the palette universe and the Hamming form of soficity.
* The 42-line shared block is byte-identical to the WIP solution's block at
  origin/main 14ab3c264, and both theorem statements match the pinned interface.
* The two holes are at lines 103 and 110, exactly the lines pinned in
  `scripts/check.py` `FORBIDDEN_ALLOWLIST`. The `PalomarBowenChapmanChallenge`
  lake library has no `warningAsError` and is not a default target.
* **Evidence flag.** The landing commit says the file "elaborated with exit 0 on
  MSI against the warm Mathlib oleans". It carries no success line, no md5 and
  no toolchain line, which the coordinator's landing rule requires. The landed
  blob's md5 is `ab2b85bc9ecb06e1728aa07917d82420`; the next build of the
  challenge should quote it with its success line. Sent to `bc-palomar`. The
  stale-olean rule does not bite here, because the file imports Mathlib only.
* **Pending for the solution.** When the solution gains the endpoint import, its
  import closure grows by thousands of modules. That is where the LIX entry's
  instance-capture mismatch came from, so the statement-match drivers (WIP
  `scripts/PalomarBowenChapman{ChallengeType,SolutionType}.lean`) must be rerun
  at that point, not only now.

**(d) Landed: the Dynamics base layer, 5e2c62ed1, root-wired. No defect.**
* Seven modules: `Surjunctivity`, `Transplant`, `SurjunctivitySubgroup`,
  `FiniteMemory`, `CosetSlice`, `SurjunctivityResiduallyFinite`,
  `SurjunctivityTransfer`. All seven root imports are on origin/main.
* The evidence meets the rule:
  * the pinned v4.32.0 toolchain with `-DwarningAsError=true`;
  * one invocation doing upload, md5 and compile;
  * `exit=0` with the olean present for every module;
  * `#print axioms` giving `[propext, Classical.choice, Quot.sound]` for
    `IsSurjunctive.surjective_localMap`, `isSurjunctive_of_isResiduallyFinite`,
    `isSurjunctive_of_residuallyFinite`, `IsSurjunctive.of_mulEquiv`,
    `IsSurjunctive.of_injective`, `IsSurjunctive.subgroup` and
    `isResiduallyFinite_iff_group_residuallyFinite`.
* All seven md5s quoted in the message equal the landed blobs.
* Stale oleans do not apply. The one repository dependency outside the batch is
  `Algebra.FiniteResidual`, which is unchanged since a7bf5d4fc and which, as the
  message states, was compiled privately from main's source. The remaining
  imports are modules of the same batch.
* Content: `shift`, `IsEquivariant`, `localMap` and `IsSurjunctive` are exactly
  the definitions checked in F2(e), and `isSurjunctive_of_residuallyFinite
  [Group.ResiduallyFinite G]` is the form the endpoint scaffold uses.

**(e) Landed: `Dynamics/SiteStrata` and `Dynamics/SubsetSchedule`, 0bfc073cd,
root-wired. No defect.**
* Both import Mathlib only. The message quotes "Build completed successfully
  (845 jobs), exit 0" from `scripts/remote-build.sh`, and both quoted md5s equal
  the landed blobs.
* The Mathlib pin is unchanged since a7bf5d4fc, so stale oleans do not apply.
  Both root imports are on origin/main, so the orphan scan stays clean.

**(f) Landed: `Kazhdan/SemidirectProductKazhdan`, 3d4569114, root-wired. No
defect.**
* The statement matches the pinned permanence theorem, stated for
  `{N Q : Type u}` at `HasKazhdanPropertyT.{u, v}`.
* Evidence: pinned toolchain, `-DwarningAsError=true`, `REAL_EXIT=0` and the
  olean written for the module and both repository dependencies. The quoted md5
  equals the landed blob.
* Stale oleans do not apply. The repository closure is exactly `Kazhdan/Kazhdan`
  and `Kazhdan/KazhdanFixedSpace`, both compiled privately. Their quoted md5s
  equal their blobs, and the claimed source base a6622e53c agrees with the
  landing parent on both.

**(g) Landed: `BowenChapman/LaurentPair`, 031156388, root-wired. No defect.**
* Content as in F4(b). The landed consumer lemmas are `substitution_single`,
  `actorAction_coe_apply`, `actorAction_elementaryUnit`, `peripheralHom`,
  `peripheralHom_injective`, `peripheral_eq_range` and `mem_peripheral_iff`.
* Evidence: `-DwarningAsError=true`, `lp_EXIT=0`, the olean written, and the
  quoted md5 equals the landed blob.
* The repository closure is `Leavitt/ElementaryGroup` alone, which has no
  repository imports. It was compiled privately from blob c420409ca6f3, which is
  its blob both at the claimed base a9b25c312 and at the landing parent. The
  evidence names that dependency by git blob id rather than md5, which is
  equivalent.

**(h) Landed: `BowenChapman/ResiduallyFiniteSubstitution`, dfa8d5e7b,
root-wired. No defect; it fixes F3(b).**
* `CongruenceQuotient.residuallyFinite_semidirectProduct_of_expSubst` is
  general. Take a finite nontrivial commutative ring `k`, subgroups `N` of the
  units of `Matrix ι ι k[ℤ^ι]` and `Q` of the units of `Matrix ι ι ℤ`, and an
  action `φ` that substitutes exponents entrywise (hypothesis `hφ`). Then
  `N ⋊[φ] Q` is residually finite. `hφ` is structural, not a literature input.
* `eq_one_of_forall_mulVec_substMod_eq` is the two-test separation proposed in
  F3(b): the standard basis columns force `L = 1`, and then monomials force
  `R = 1`.
* The WIP consumer `LaurentPairResiduallyFinite` discharges `hφ` through
  `substitution_apply_eq_expSubst`, proved by induction on Laurent polynomials.
  Both `substitution` and `expSubst` map the domain along `v ↦ M *ᵥ v`, and
  `k = ZMod 2` is finite and nontrivial.
* Evidence: Mathlib-only imports, pinned toolchain, `-DwarningAsError=true`,
  `EXIT=0`, the olean written, and the quoted md5 equals the landed blob.

**(i) Landed: `Sofic/WreathCentralizerNormalization`, 2d5427380, root-wired. No
defect.**
* The algebraic core as in F4(b), plus `wreath_quotient_fg`.
* Evidence: `-DwarningAsError=true`, `EXIT=0`, the olean written, and the quoted
  md5 equals the landed blob.
* The repository closure is `Algebra/FiniteResidual`,
  `Algebra/PermutationalWreath` and `Algebra/PermutationalWreathSimple`. All
  three quoted md5s equal their blobs at the landing parent. Each blob equals
  main's at 09-11 18:21 CDT (d9a4490a7), the end of the clone's build window, so
  the clone's oleans were built from current sources.

**(j) Landed: the Dynamics upper layer, 684f9d301, root-wired. No defect.**
* Six modules: `CosetRegion`, `StratifiedPeeling`, `FinitarySite`,
  `FinitaryTransplant`, `FinitarySurjunctivity` and `WreathFinitarySite`. Six
  root imports are added, and the only deletions are the six WIP snapshots.
* Evidence:
  * all six quoted md5s equal the landed blobs;
  * the private probe used `-DwarningAsError=true` and exited 0 for each module;
  * the mutexed `scripts/remote-build.sh` run reports "Build completed
    successfully (1187 jobs)";
  * `FinitarySite.isSurjunctive` and `isSurjunctive_wreath` depend on
    `[propext, Classical.choice, Quot.sound]`.
* The repository dependencies are the Dynamics base layer and
  `Algebra/PermutationalWreath`. The mutexed build rebuilds any stale
  dependency, so stale oleans do not apply.
* Content: the landed `FinitarySite` fields are exactly the ones F3(d) was
  checked against, and `wreathFinitarySite` is a compiled instance, so the
  fields are satisfiable. The site fields are structural hypotheses, not
  literature inputs.

**(k) Landed: `BowenChapman/LaurentPairResiduallyFinite`, e728fe4e7,
root-wired. No defect.**
* It proves `ambient_residuallyFinite : Group.ResiduallyFinite Ambient`, the
  pinned statement, through `substitution_apply_eq_expSubst` and the general
  theorem of F4(h).
* Probe evidence: the message cites probe 0912-115423-96573, GREEN at base
  79408b79a. The landed md5 `cdfaedf4…` is in `bc-rf.green.0912-115423-96573`,
  whose `# mods` names the module and whose `# PROBE` line is GREEN.
* The repository import closure is `LaurentPair`,
  `ResiduallyFiniteSubstitution` and `Leavitt/ElementaryGroup`. Each blob at the
  record base equals its blob at the landing parent, and the base is an
  ancestor of the landing.
* One root import is added, and nothing is deleted.

**(l) Landed: `Dynamics/DoubleKernel`, `DoubleConsequences`,
`DoubleFinitarySite`, 53d1db321, root-wired. No defect.**
* `isSurjunctive_symmetricDouble {G : Type w} [Group G] (Γ : Subgroup G)
  (hG : IsSurjunctive G) : IsSurjunctive (SymmetricDouble G Γ)` matches the
  pinned interface.
* The instance supplies every `FinitarySite` field with the maps checked in
  F3(d): site groups free on `S \ {x₀}`, `kernelSupport` containing `x₀`
  (`base_mem_kernelSupport`), detection, finite support and stabilizer
  invariance. Residual finiteness of the site groups comes from the repo's
  `Sofic/FreeGroupResiduallyFinite`.
* Probe evidence: the message cites probe 0912-115538-1495 at base 4d8097c38,
  with "Build completed successfully (1398 jobs); PROBE GREEN; REAL_EXIT=0". All
  three landed md5s are in `bc-double-surj.green.0912-115538-1495`, whose mods
  name all three modules.
* The repository import closure has 21 modules. None changed between the record
  base and the landing parent, and the base is an ancestor of the landing.
* Three root imports are added, and nothing is deleted.

**(m) Landed: `BowenChapman/LaurentPairInfranormal`, 8d36818d4, root-wired. No
defect.**
* `peripheral_isInfranormal : IsInfranormal Peripheral` and
  `peripheral_not_normal : ¬ Peripheral.Normal` are the pinned statements.
* Probe evidence: the message cites probe 0912-115614-4108 at base 4d8097c38,
  PROBE GREEN, REAL_EXIT=0. The landed md5 `5d99e13d…` is in
  `bc-pair.green.0912-115614-4108`, which carries `# PROBE GREEN` and names the
  module.
* The repository import closure is `LaurentPair`, `Leavitt/ElementaryGroup` and
  `Sofic/InfranormalCompressionPair`. None changed between the record base and
  the landing parent, and the base is an ancestor of the landing.
* One root import is added. The only deletion is its WIP snapshot.

**(n) Landed: `BowenChapman/LaurentPairKazhdan` and `LaurentPairGeneration`,
3e8c96515, root-wired. No defect.**
* `ambient_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} Ambient`,
  `peripheral_hasKazhdanPropertyT : HasKazhdanPropertyT.{0, 0} ↥Peripheral`,
  `ambient_fg : Group.FG Ambient` and `instance ambient_countable : Countable
  Ambient` are the pinned statements.
* Probe evidence: the message cites probe 0912-115559-3074 at base 4d8097c38,
  with "Build completed successfully (3932 jobs)", PROBE GREEN and REAL_EXIT=0.
  Both landed md5s are in `bc-kazhdan.green.0912-115559-3074`, which carries
  `# PROBE GREEN` and names both modules.
* The repository import closure has 226 modules, including the EJZ property (T)
  theorem. None changed between the record base and the landing parent, and the
  base is an ancestor of the landing.
* Two root imports are added. The only deletions are the two WIP snapshots.

**(o) Landed: the pending Bowen–Chapman gate registration, 73f646f13. No
defect.**
* `Palomar/comparator-bowen-chapman.json` is added to `PALOMAR_PENDING_CONFIGS`,
  not to `PALOMAR_CONFIGS`, which still holds only the LIX configuration.
* The self-test gains four planted defects: a project-local import in the
  challenge, a shared block edited on one side, a missing `_of` form, and a
  fourth permitted axiom.
* `scripts/check_palomar_statement_match.sh` now loops over `BowenChapman`.
* `palomar-check.yml` builds both Bowen–Chapman libraries and runs
  `PalomarBowenChapmanAxioms.lean`, and the job fails when that step fails.
* Neither library is a default target. The only deletion is the WIP gate patch.

**Landing evidence required from here on**, per the coordinator's rule:
* the pinned v4.32.0 toolchain with `-DwarningAsError=true`;
* the md5 of the exact landed bytes, checked in the same invocation as the
  build;
* repository dependencies from oleans built from source identical to main,
  never from the 30 August shared oleans for modules changed since;
* success lines and md5s quoted in the commit message.

**Mandatory guards for every plumbing push** (coordinator, after F5):
* the exit status of `read-tree` is checked;
* the private index holds as many entries as the base tree;
* `git diff --no-renames --diff-filter=D BASE NEW` is empty unless a deletion is
  intended.

**Still to review as they land:** `WreathWitness` and the sequential wreath
consumer (`bc-wreath`); the four Theorem 4.1 lanes; `bc-assembly`; and the
unsuffixed `bc-palomar` solution, together with its move from
`PALOMAR_PENDING_CONFIGS` to `PALOMAR_CONFIGS` and a rerun of the
statement-match drivers after the endpoint import.

## F5. Main was emptied and restored

**Status: restored, audited, no content lost.**

* **The event.** Commit becc912bd (11:10:52) deleted 27,762 files and 3,829,822
  lines, leaving only `research/`. `git diff --shortstat ce16f64eb becc912bd`
  shows this, and the GitHub tree API showed the live tip 1e52c3688 holding
  only `notes/` and `research/`. Five more commits landed on the emptied base
  before the restore. The coordinator traced the cause to a shared landing
  script whose private index was built by a `read-tree` that failed while the
  Mac disk was full (418 MiB free); that script is now gated. No campaign lane
  pushed on the emptied base.
* **The restore.** Commit 3f71a3a50 has parent bff8f642a and 0 deletions. The
  GitHub compare `ce16f64eb...3f71a3a50` lists 23 files and no removals, exactly
  the paths added or edited after the collapse. The coordinator measured 0
  missing ce16f64eb paths and equal root imports (4530) at b7fe2241a.
* **Edits against ce16f64eb.** Six paths show deletions against ce16f64eb,
  each small and each reading as the owner's edit rather than a stale copy:
  `OddPDiagonalSrc.lean.txt`, `LIXStepDGenReal.lean.txt`, `tpmc.c`,
  `defect-window-automata-2026-09-12.md`,
  `nested-rigid-defects-force-nonsurjunctivity.md` and
  `wip/bowen-chapman/.../FixedPointNormalizationPatching.lean`. Only the last
  belongs to this campaign.
* **Campaign landings.** Every campaign landing before ce16f64eb survives with
  its blob: 031156388, 1ad7aa663, 3d4569114, dfa8d5e7b, 2d5427380 and this
  review file.

An informal pass of the permanence chain by another team is not a Lean
verification; the Lean is reviewed here independently.

## F6. The shared probe infrastructure

**Status: sent to `bc-infra`; (1) open, (2) and (3) are audit rules applied
here.** I read `bcprobe.sh` in the campaign scratchpad and
`tools/bc-swarm/remote/bcjob.template.sh` at 924105b04.

* **(1) Failed probes can write a record named `.green.`. Confirmed.**
  `bcprobe.sh` writes `<lane>.green.<tag>` whenever the job reports at least
  one compiled overlay file, whatever the `# PROBE` line says. The job lists
  compiled files after `lake build` whatever its exit code. Evidence:
  `lanes/kt-norm-paper.green.0912-120052-26096` contains `# PROBE FAILED rc=1`.
  The planted-type-error calibration left no record only because the plant
  produced no olean at all; a green helper with a red target in one probe would
  leave a `.green.` file. **Audit rule:** a record counts only if it contains
  `# PROBE GREEN`. The two records cited by landings so far (F4(k), F4(l)) do.
* **(2) The already-green shortcut ignores the base.** A probe of bytes and mods
  already recorded green at any earlier base is skipped. **Audit rule:** compare
  the landed modules' import closures between the record base and the landing
  parent, as done in F4(k) and F4(l).
* **(3) Palomar libraries build without `-DwarningAsError=true`.** For a Palomar
  module, PROBE GREEN does not exclude an incomplete proof, which there is only a
  warning.
  **Audit rule:** Palomar solution landings also need the axiom driver's output.
* **Checked, no defect:**
  * the base refuses a gutted tree;
  * the synced paths must equal the tree (G1–G4);
  * the manifest md5 is checked;
  * overlays are restricted to `GroupApproximation/**/*.lean`, `Palomar/*.lean`
    and `lakefile.toml`;
  * PROBE GREEN requires exit code 0 and "Build completed successfully";
  * an olean restored from the artifact cache counts as compiled, which is sound
    because the cache key includes the source hash;
  * the calibration record's md5 `9f6a8f83…` equals main's
    `Dynamics/Surjunctivity.lean`.

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
