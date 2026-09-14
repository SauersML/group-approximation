# Lane ms-core-3: simple_kazhdan_sofic_group.tex, "Finite models" tail (tex 146–153 at bf961c128)

Target: origin/main `simple_kazhdan_sofic_group.tex` at bf961c128 (340 lines, md5 7b3dc4ec92b4581553bc0dc2b0edcb99). Rows keyed
`LINE:<l>@bf961c128` in `metadata/sk-census-rows/ms-core-3.tsv`.

CLAIM tex 146–153 (entrywise finite models of G, the injective partial homomorphism into GL_{3N}(F₂), "Thus G is LEF", sofic and hyperlinear models) — split proposed to ms-units 2026-09-13 ~19:05 (ms-units keeps tex 118–145); new modules under GroupApproximation/Manuscript/SimpleKazhdanSofic/ once the ledger lands

## Text versions

- bf961c128 (18:54, 340 lines): range 146–153. Superseded.
- 2050a8eed (19:29, 290 lines, md5 65d47cb4…): range 130–134. Superseded before any row landed.
- **e80dcf20a (19:39, 386 lines, md5 4ad4921253626a4f858866c716a13385): the current tip.** Lanes are ranged by section heading
  and rows keyed by 12-hex sentence hash (main's protocol, 19:45). `SK_SENTENCE_CENSUS.tsv` on origin is still at bf961c128,
  so no rows land until skf-census regenerates at the tip.

CLAIM "Finite models" tex 147–166 (marked limits of SL_{3N_ℓ}(F₂), G LEF, expanders, LEF ⇒ sofic ⇒ hyperlinear), then tex
168–177 (the L(G) consequences) — re-split proposed to ms-units 2026-09-13 ~19:50; ms-units keeps 117–145.

## Ledger at e80dcf20a ("Finite models", my part; keys pending the census)

| tex | sentence (abridged) | carriers on origin | status (planned) |
|---|---|---|---|
| 147–150 | free algebra F = F₂⟨t_±, t_a⟩; ring homomorphisms π : F → R and ρ_ℓ : F → M_{N_ℓ}(F₂); both onto | to check: `FreeAlgebra.lift`, generation of R (ct-involution's range) | open |
| 151–153 | ρ_ℓ onto: the rotations of y_ℓ are distinct, so products of P^iD_ℓ(e_a)P^{-i} give every diagonal matrix unit, and with P every matrix unit | none known | open |
| 153–157 | G and EL_3(M_{N_ℓ}(F₂)) = SL_{3N_ℓ}(F₂) are quotients of EL_3(F) with compatible generators; transvections generate SL, and in-block ones are commutators between blocks | `elementaryGroupMap_surjective_of_surjective` (Leavitt/ElementaryGroup); EL = SL over a field (`AlgebraicK.mem_elementaryGroup_of_detUnits_eq_one`?) | open |
| 157–161 | words of length L have entries of degree ≤ L; φ_ℓ∘π = ρ_ℓ on them; a word is trivial in G iff trivial in SL_{3N_ℓ}(F₂) for large ℓ | consumes ms-units' φ_ℓ Prop | open |
| 162–163 | these finite simple groups converge to G in the space of marked groups, and G is LEF | marked-group carriers to grep; `isLEF_of_forall_finite_model` | open |
| 163–164 | EL_3(F) has (T), so the Cayley graphs form expanders [Kassabov] | `ejz` (EL_n of f.g. rings); the expander step needs a carrier | open |
| 164–166 | LEF groups are sofic, and sofic groups are hyperlinear [Pestov] | `isSofic_of_isLEF`, `isHyperlinear_of_isSofic` (root-imported) | formalized |
| 168–177 | L(G) ↪ R^ω [Ozawa 7.1]; ICC and not RF; II₁ factor; McDuff; Brown's formulation; Kirchberg 1.1 ⇒ no factorization property; no LLP [Ozawa p.527] | to grep | open |

Landed carrier (3d1ce154d, `Manuscript/SimpleKazhdanSofic/FiniteModelsGroup`): entrywise models into GL_{n×N}(K), with
closed endpoints printedFiniteModelsGeneralLinear and printedFiniteModelsLEFSoficHyperlinear. The injective-map sentence it
carried at bf961c128 and 2050a8eed does not survive at e80dcf20a; "G is LEF" is now printed through marked limits. It stays
valid as a general carrier, but it is no longer the printed route.

## Sub-leaf claims at e80dcf20a (ownership checked 2026-09-13 ~19:55: no module in Manuscript/SimpleKazhdanSofic covers them)

CLAIM L1, tex 153–157: EL_3(M_{N}(F₂)) = SL_{3N}(F₂), because transvections generate SL and in-block transvections are commutators between blocks → GroupApproximation/Manuscript/SimpleKazhdanSofic/MarkedLimitSpecialLinear.lean
CLAIM L2, tex 147–150 and 163: the free algebra F = F₂⟨t_±, t_a⟩ is a finitely generated ring, so EL_3(F) has (T) through `ejz` → GroupApproximation/Manuscript/SimpleKazhdanSofic/FreeAlgebraKazhdan.lean

Carriers to reuse: `AlgebraicK.ker_detUnits`, `elementaryBlockGroup_map` / `elementaryBlockEquiv`, `ejz`,
`isFinitelyGeneratedRing_iff_finiteType_int` (the UniversalOneSidedPairRing idiom), and ms-intro-3's `Setting` (R, G,
letterIndicator). The next leaves are ρ_ℓ onto, words of length L, marked convergence and expanders; they will be claimed
after ms-units' `FiniteModelsRing` names land.

## Keys at e80dcf20a (census 09e580c38, hash-keyed rows)

| key | tex | sentence (abridged) | carrier | status |
|---|---|---|---|---|
| `20e867674c81` | 147–150 | free algebra F = F₂⟨t_±, t_a⟩, ring homomorphisms π : F → R and ρ_ℓ : F → M_{N_ℓ}(F₂) | L2 `FreeAlgebraKazhdan` (F finitely generated, in probe); π, ρ_ℓ not built | open (rowed after L2 lands) |
| `3736b79d29b0` | 150 | "Both are onto." | none | open |
| `8928299f8375` | 151–153 | rotations distinct ⇒ every diagonal matrix unit, with P every matrix unit | none | open |
| `6860e6b8a6ad` | 153–155 | G and EL_3(M_{N_ℓ}(F₂)) = SL_{3N_ℓ}(F₂) are quotients of EL_3(F) with compatible generators | L1 `printedBlockElementarySpecialLinear` (the equality) | partial (rowed) |
| `13bf024677ad` | 155–157 | the equality holds since transvections generate SL and in-block ones are commutators between blocks | L1 `printedBlockElementarySpecialLinear`, `AlgebraicK.ker_detUnits`, `elementaryBlockGroup_map` | formalized (rowed) |
| `5600d3017a0c` | 157–159 | words of length L have entries of degree ≤ L; φ_ℓ∘π = ρ_ℓ on them | none (needs ms-units' φ_ℓ) | open |
| `8166a301ad3d` | 159–161 | a word is trivial in G iff trivial in SL_{3N_ℓ}(F₂) for large ℓ | none | open |
| `60605fdb5e61` | 162–163 | convergence in the space of marked groups; G is LEF | none | open |
| `5538b733c423` | 163–164 | EL_3(F) has (T), so the Cayley graphs are expanders [Kassabov] | L2 gives (T) for EL_3(F) | **oa-expanders** (main, 20:15), over L1/L2 |
| `b565e2b44061` | 164–166 | LEF ⇒ sofic ⇒ hyperlinear [Pestov] | `isSofic_of_isLEF`, `isHyperlinear_of_isSofic` | formalized (rowed) |
| `b55725a40939` … `1fe81fb1330c` | 168–177 | L(G) ↪ R^ω, ICC and not RF, II₁ and McDuff, Brown's formulation, Kirchberg, no factorization property, no LLP | to check | open |

- 09-13 ~20:03: an API outage killed the lane mid-turn. Resumed 20:15.
- 09-13 20:2x: **LANDED 8c266ff3d**, `Manuscript/SimpleKazhdanSofic/MarkedLimitSpecialLinear.lean`; probe 0913-195736-89868 GREEN
  with a BUILT line, 0 axiom-allowlist violations and no sorry. Queued for wiring.
  `elementaryBlockGroup_map_eq_ker_detUnits` (any field, N ≥ 1) and the closed `printedBlockElementarySpecialLinear` (F₂).
- L2 `FreeAlgebraKazhdan` (attic ea16f9222): the first probe (0913-202426-56850) is red in the scalar case of the free-algebra
  induction; fixing. Its `.green.` record lists only the already-landed L1 and is not evidence for L2.
