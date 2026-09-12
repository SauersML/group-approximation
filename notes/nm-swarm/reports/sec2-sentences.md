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
| Kazhdan/GHWArchimedeanSeparation | spectral reduction; `SeparationFinite` for every g; κ·\|log a\| ≤ μ(Δ) with κ = 2φ(1) | on main (82942cbb9), not compiled: imports Minkowski, which was red at probe 0911-235228-11830 |
| Kazhdan/GHWArchimedeanBound | adapters `archimedeanAffineBound_places(_fin)` compiled; `separationFinite`, `ghwArchimedeanAffineBound` not compiled | on main (7087bee54); imports Walls, red at dgo-geometric probe 0912-092049-2822 |
| Algebra/GHWFrobeniusSeparable | step (4): `GroupApproximation.GHW.exists_separable_frobenius_embedding` | compiled: probe 0912-092155-16446 GREEN at base 87ab7e225; axioms propext, Classical.choice, Quot.sound |

Step (4), exact statement:
`theorem GroupApproximation.GHW.exists_separable_frobenius_embedding (L K : Type*) [Field L] [Field K] [Algebra L K]
[FiniteDimensional L K] (p : ℕ) [ExpChar L p] : ∃ (K' : IntermediateField L K) (e : ℕ) (φ : K →+* K'),
Algebra.IsSeparable L K' ∧ ∀ x : K, ((φ x : K') : K) = x ^ p ^ e`.
The proof takes K' := separableClosure L K and e := the exponent of K / K'.  The map φ is
`IsPurelyInseparable.iterateFrobenius`.

Next: when dgo-geometric reports Minkowski and Walls green, probe Separation and Bound as one batch, fix, and land.

## Census

Rows: `metadata/nm-census-rows/sec2-sentences.tsv`.  The four sentences with no declarations
(6a52924d8260, db7009c5a941, 2a0e1987e5c2, a1f7e96658eb) are setup or motivation and are graded structural.

## Traps found

- `map_sub`/`map_mul`/`map_zero` on `normMatrixCStarCoronaMk` time out in instance search; `RingHom.map_*` compiles.
- `map_continuous` on `→⋆ₐ[ℂ]` into a norm matrix corona finds no ContinuousMapClass even under
  `open scoped CStarAlgebra`; `LinearMap.mkContinuous` with `NonUnitalStarAlgHom.norm_apply_le` compiles.
- `•` on `BoundedMatrixSequence (fun n ↦ cornerModel …)` times out; Nonempty binders plus type ascriptions fix it.
- `#audit_closed_axioms` rejects any theorem whose type starts with a binder: wrap endpoints as named Props.
