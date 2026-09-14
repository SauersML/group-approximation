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
