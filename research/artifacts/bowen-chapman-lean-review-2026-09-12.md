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

## F4. Landed code and early drafts

As of `origin/main` 49fe43fa6 three landings touch the campaign: the Palomar
challenge (6ae077316), the Dynamics base layer (5e2c62ed1) and the site-strata
leaves (0bfc073cd). Everything else is a WIP snapshot under
`wip/bowen-chapman/`.

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
  `peripheralHom_injective`. Sent. The (T) inputs are sound:
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

**Still to review as they land:** `bc-dynamics-upper` batch 2, the first
`bcprobe` landings, `bc-pair`, `bc-kazhdan`, `bc-rf`, `bc-double-surj`,
`bc-wreath`, `kt-norm-paper`, `kt-norm-repo`, `kt-norm-fixedpoint`,
`kt-norm-counting`, `bc-assembly`, and the unsuffixed `bc-palomar` solution.

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
