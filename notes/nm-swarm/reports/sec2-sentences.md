# sec2-sentences: Section 2 "One-sided compression" (tex 346-784 at 73c867c5b)

Status 2026-09-11 22:40: **done**.  Every non-structural sentence of Section 2 has a carrier that compiled.
None of these modules is imported by the root yet; they are queued for wiring.

## Modules (all `GroupApproximation/Manuscript/NonMFSentences/`)

| module | carries | landed (compiled) |
|---|---|---|
| CompressionSentencesA | prop:mf-residual-calculus proof sentences; canonical maps into U(C*max(G)), U(C*r(G)); Ad(V(g)) bijection; finite / stably finite | 1b3021bfe (probe 0911-210656) |
| CompressionSentencesB | τ = lim_ω tr_{r_n} well defined, linear, unital, positive, tracial (representatives) | f88d7583 (0911-212711) |
| CompressionSentencesB2 | τ as a continuous linear functional on the corona 𝒬_r, \|τ(x)\| ≤ ‖x‖ | a0ff25d62 (0911-214558) |
| TransportCharacterizationIffSentence | x ∈ 𝒞₂(V,L) iff ‖P_n x_n − x_n‖₂ → 0 | 3d48bf8ef (0911-212047) |
| CentralCoronaCornerRanks | retained coordinates, r_n = rank(q_n) ≥ 1 | 3d48bf8ef (0911-212047) |
| HSOperatorNormGapSentences | ‖D_d − 1‖₂ = 2/√d → 0, ‖D_d − 1‖ = 2 | 1b3021bfe (0911-212711) |
| KazhdanProjectionExistenceSentence | e_L central star projection fixing exactly the invariant vectors in every representation, every universe | f88d7583 (0911-212711) |
| MFRadicalQuotientBlockSumSentences | tex 372-379: the block-sum family, asymptotically multiplicative, separating; G/Rad_MF(G) has trivial residual | a0ff25d62 (0911-214558) |
| HSNullNormalSubgroupSentences | tex 404-412 with every clause and the three displays; the normal subgroup = hsKernel | 477ebb4a1 (0911-220408) |
| DyadicReductionSeparation | ℤ[1/2] →+* ℤ/m (m odd), V →* GL₄(ℤ/m) separates V, so V is RF and MF | 477ebb4a1 (0911-220408) |
| NormalKazhdanUltrafilterRoute | thm:normal-kazhdan, last paragraph sentence by sentence; endpoint `manuscriptNormalKazhdanRadical_ultrafilterRoute : NormalKazhdanRadical` | 4bc478e03 (0911-221323) |

`DyadicReductionSeparation` imports `Sofic/AffineHNNBaseRealization`, which is also not wired.

## GHW Theorem 4 (tex 1146-1147)

Status 2026-09-12 09:25.  Printed sentence: "Every countable subgroup of $\mathrm{GL}_2$ over a field has the
Haagerup property~\cite[Theorem~4]{GHW}".  No literature inputs are allowed, so the theorem is proved in Lean.  sec2 owns
the modules below.  The Minkowski and Walls modules belong to dgo-geometric; the non-archimedean steps (1)-(5) belong
to jacobson, except step (4), which sec2 wrote.

| module | carries | state |
|---|---|---|
| Kazhdan/GHWArchimedeanWedge | wedge geometry at the archimedean places | compiled (4197466c8) |
| Kazhdan/GHWArchimedeanSeparation | spectral reduction; `SeparationFinite` for every g; κ·\|log a\| ≤ μ(Δ) with κ = 2φ(1) | compiled: probe 0912-093859-21657 BUILT at 448d1bf45 (base 0ac9f4538) |
| Kazhdan/GHWArchimedeanBound | adapters `archimedeanAffineBound_places(_fin)` compiled; `separationFinite`, `ghwArchimedeanAffineBound` | compiled: probe 0912-094259-57545 GREEN at 6d8971521 (base 9b29a2730); both endpoints pass `#audit_closed_axioms` |
| Algebra/GHWFrobeniusSeparable | step (4): `GroupApproximation.GHW.exists_separable_frobenius_embedding` | compiled: probe 0912-092155-16446 GREEN at base 87ab7e225; axioms propext, Classical.choice, Quot.sound |

Step (4), exact statement:
`theorem GroupApproximation.GHW.exists_separable_frobenius_embedding (L K : Type*) [Field L] [Field K] [Algebra L K]
[FiniteDimensional L K] (p : ℕ) [ExpChar L p] : ∃ (K' : IntermediateField L K) (e : ℕ) (φ : K →+* K'),
Algebra.IsSeparable L K' ∧ ∀ x : K, ((φ x : K') : K) = x ^ p ^ e`.
The proof takes K' := separableClosure L K and e := the exponent of K / K'.  The map φ is
`IsPurelyInseparable.iterateFrobenius`.

Proved without hypotheses (probe 0912-094259-57545; the axioms of both are within the classical allowlist):
`GroupApproximation.GHW.separationFinite : Walls.SeparationFinite` and
`GroupApproximation.GHW.ghwArchimedeanAffineBound : GHWArchimedeanAffineBound`.  Through `archimedeanAffineBound_places_fin`
the second discharges the `(A, hA)` input of `hasHaagerupProperty_of_places`.  Separation and Bound are not root-wired.
Algebra/GHWFrobeniusSeparable is in the root-wiring wave; edits to it land with NM_ATTIC until a probe is green.

## GHW char 0: countably many places

Status 2026-09-12.  The lead assigned sec2 one whole file of the char-0 half.  dgo-geometric owns GHWCharZeroFiniteness
and GHWCharZero and agreed the statements below; jacobson owns char p.  A finite set of σ does not suffice: for ℤ[t] the
finiteness hypothesis of `hasHaagerupProperty_of_places` fails.  So the σ are countable, with bounds that depend on
the place.

| module | carries | state |
|---|---|---|
| Kazhdan/GHWCountablePlaces | `AffineAction.smul`, `countableSum`, `exists_weights`; `Haagerup.hasHaagerupProperty_of_countable_sum`; `GHW.hasHaagerupProperty_of_countable_places` | landed unverified at 3a0808fa5; probe running |

Exact statements:
`theorem GroupApproximation.Haagerup.hasHaagerupProperty_of_countable_sum {G : Type u} [Group G] [Countable G]
{ι : Type} [Countable ι] (A : ι → AffineAction.{u, v} G)
(hproper : ∀ C : ι → ℝ, {g : G | ∀ i, ‖(A i).b g‖ ≤ C i}.Finite) : HasHaagerupProperty.{u, v} G`

`theorem GroupApproximation.GHW.hasHaagerupProperty_of_countable_places {K : Type} [Field K] {Γ : Type} [Group Γ]
[Countable Γ] (ρ : Γ →* GL (Fin 2) K) (hρ : Function.Injective ρ) {k : ℕ}
(v : Fin k → AddValuation K (WithTop ℤ)) (π : Fin k → K) (hπ : ∀ j, v j (π j) = 1)
{ι : Type} [Countable ι] (σ : ι → (K →+* ℂ)) (S : Set K)
(hS : ∀ (γ : Γ) (a b : Fin 2), ((ρ γ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) a b ∈ S)
(hfin : ∀ (C : ι → ℝ) (N : ℕ), {a : K | a ∈ S ∧ (∀ i, ‖σ i a‖ ≤ C i) ∧
∀ j, (((-(N : ℤ)) : ℤ) : WithTop ℤ) ≤ v j a}.Finite) : HasHaagerupProperty.{0, 0} Γ`

Weights: enumerate G by e and inject ι into ℕ by f.  Put M_i = ∑_{k ≤ f i} ‖b_i(e k)‖ and w_i = 2^{-f i}/(1 + M_i).
Then (w_i b_i(g))_i is in ℓ².  A bound ‖b g‖ ≤ R gives ‖b_i g‖ ≤ R/w_i for every i.

## Census

Rows: `metadata/nm-census-rows/sec2-sentences.tsv`.  The four sentences with no declarations
(6a52924d8260, db7009c5a941, 2a0e1987e5c2, a1f7e96658eb) are setup or motivation and are graded structural.

## Traps found

- `map_sub`/`map_mul`/`map_zero` on `normMatrixCStarCoronaMk` time out in instance search; `RingHom.map_*` compiles.
- `map_continuous` on `→⋆ₐ[ℂ]` into a norm matrix corona finds no ContinuousMapClass even under
  `open scoped CStarAlgebra`; `LinearMap.mkContinuous` with `NonUnitalStarAlgHom.norm_apply_le` compiles.
- `•` on `BoundedMatrixSequence (fun n ↦ cornerModel …)` times out; Nonempty binders plus type ascriptions fix it.
- After `rw [comapHom_b, wallAction_b]` the norm is still taken at the carrier `(A.comapHom ρ).E`, so `rw [norm_smul]` finds
  no occurrence.  Prove the identity in `Lp ℝ 2 shellMeasure` and close with `exact`.
- `push_neg` is deprecated at the pin, and warningAsError makes it an error; use `push Not at h`.
- `#audit_closed_axioms` rejects any theorem whose type starts with a binder: wrap endpoints as named Props.
