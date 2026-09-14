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

## Re-scope at 9047d0d3c (20:31, 618 lines, md5 274f19367f7f706b05c017af721c3884; census regenerated at 9047d0d3c, d11e91f6e)

- WITHDRAWN: my claim on the old tex 168–177, now the "Brown's formulation" subsection. Main's OA lanes (roster 20:15/20:35)
  own it: oa-ozawa71 (L(G) ↪ R^ω), oa-mcduff (ICC, II₁, McDuff), oa-kirchberg and oa-llp. No ICC module was written.
- skf-cite holds the closed wrappers for "LEF groups are sofic [Pestov, Ex. 4.5], and sofic groups are hyperlinear
  [ElekSzabo, Thm 2]", a rewritten sentence. My row `b565e2b44061` was keyed at e80dcf20a and does not carry to the new
  wording.
- oa-expanders owns "its finite quotients form a family of expanders [Margulis, Kassabov]" over L1/L2.
- ct-two-ended owns "and G is LEF" (`isLEF_of_isMarkedLimit`, `Manuscript/SimpleKazhdanSofic/MarkedLimitLEF`) and the thm:main
  assembly (MainAssembly, bf15b32cf).

CLAIM marked convergence (tex 162–180 at 9047d0d3c): π : F → R and ρ_ℓ : F → M_{N_ℓ}(F₂); ρ_ℓ onto; EL_n(F) generated by
e_ij(1), e_ij(τ); words of length λ have entries of degree ≤ λ; φ_ℓ∘π = ρ_ℓ on them for large ℓ; a word is trivial in G iff
trivial in SL_{nN_ℓ}(F₂) for large ℓ; packaged as ct-two-ended's `IsMarkedLimit s σ` for EL_n, n ≥ 3. New modules under
Manuscript/SimpleKazhdanSofic/, consuming ms-units' asymptotic φ_ℓ once it lands.

- Printed generality: `thm:main` (l.67–68) states the marked limits for EL_n, every n ≥ 3, with SL_{nN}(F₂). L1 and L2 are
  re-stated for every n ≥ 3 and LANDED at 37646c582 (probe 0913-203429-33235 GREEN, both BUILT).

## Rows at 9047d0d3c (census d11e91f6e)

- Kept: `13bf024677ad` formalized. The n ≥ 3 note is added.
- New: `414df07890f1` partial, "So G and EL_3(M_{N_ℓ}(F₂)) = SL_{3N_ℓ}(F₂) are quotients of EL_3(F), which is generated by …".
  The equality is carried; the quotient maps and the generation are not.
- Dropped: `6860e6b8a6ad` (rewritten into `414df07890f1`), and `b565e2b44061` (rewritten into `89a5cc12fe75`, which is skf-cite's).

CLAIM marked convergence module GroupApproximation/Manuscript/SimpleKazhdanSofic/MarkedConvergence.lean (keys `d6692afc094a`,
`0f6fc65eeadb`, `8166a301ad3d`; ownership checked at 21:3x: no other lane lists the path, and no SimpleKazhdanSofic module uses
`FreeAlgebra.lift`). Route: for abstract asymptotic models φ_ℓ (additive, unital, eventually multiplicative on each pair,
eventually nonzero on each nonzero element) and ring homomorphisms π : F → R and ρ_ℓ : F → M_ℓ that agree with φ_ℓ ∘ π on the
letters, free-algebra induction gives φ_ℓ ∘ π = ρ_ℓ eventually on every element. Entrywise, a word is trivial in GL_n(R) iff it
is trivial in GL_n(M_ℓ) for large ℓ. This is the third clause of ct-two-ended's `IsMarkedLimit`. The instantiation at ms-units'
`AsymptoticModels` (FiniteModelsAsymptotic, attic e256441f0) follows once it lands. The generation clauses (π and ρ_ℓ onto) are
the next leaves.

## 00:1x re-scope: tip 696c4b602 (my sections l.211–271 unchanged since 37551fd93; census at 37551fd93)

The note is restructured around thm:general (l.109). Roster TIP 23:15: ms-core-3 owns "Finite simple models" (l.211–236)
and "Proof of thm:main" (l.238–271), and absorbs ms-units (not resumed).

- WITHDRAWN: the `MarkedConvergence.lean` claim of 21:33. The file was never created. The printed route changed: nonvanishing
  is gone, and "nontrivial words stay nontrivial" is now the ultraproduct kernel argument through simplicity of G (l.226–233).
- Rows `13bf024677ad` and `414df07890f1` are gone from the census. Their sentences became `e4fd510a51c5` (EL_3(M_{N_k}) = SL,
  the same route, carried by the landed `printedBlockElementarySpecialLinear`) and `2e17cbfab2b6`. Re-key at the next census.
- ABSORBED from ms-units (roster 23:15): `FiniteModelsAsymptotic.lean` (disk draft c2f943d5, attic 598c651f1; its last two probes
  failed), the landed `FiniteModelsForwardOrbit`, `FiniteModelsLeastPeriod`, `FiniteModelsRing` and
  `MinimalSubshiftPeriodicWord`, its report `notes/sk-formal/reports/ms-units.md`, and its rows. 12 of its 14 landed row keys are
  gone from the census.

Target spellings: ct-two-ended's `GroupApproximation/Manuscript/SimpleKazhdanSofic/GeneralTheorem.lean` (attic 3ea243dda, unlanded):
- `IsMatricialVia S N φ`, `elementaryMarking`, `matricialMarking`;
- `PrintedMatricialMarkedLimitStatement`: IsMatricialVia and simplicity of EL_n(R) ⇒ IsMarkedLimit, for every n ≥ 3;
- ct-two-ended also holds `tendsto_card_of_isMarkedLimit` (N_k → ∞ as G is infinite).

CLAIM "Finite simple models" (keys 25fefb1e2ac1, 2e17cbfab2b6, cbc0b3980a99, d228d6575111, a339b883c9d3, db0ff25cc298, 3d7e4722fef8,
9a9aa9313dca; the "G is LEF, N_k → ∞" half of 995620260311 and the expanders 95230f46af22 belong to ct-two-ended and oa-expanders) →
GroupApproximation/Manuscript/SimpleKazhdanSofic/MatricialMarkedLimit.lean, the producer of `PrintedMatricialMarkedLimitStatement`. Core lemmas are over explicit hypotheses
equal to IsMatricialVia's fields, until GeneralTheorem lands. Printed route:
1. The free algebra on τ_s, s ∈ S, with π and ρ_k both onto; EL_n(F) is generated by e_ij(1) and e_ij(τ_s).
2. φ_k ∘ π = ρ_k on each element for large k, by free-algebra induction from eventual additivity and multiplicativity. A word
   trivial in G is then eventually trivial in SL.
3. For each nonprincipal ultrafilter ω, the φ_k give a unital ring homomorphism into the algebraic ultraproduct (a RingCon
   quotient of the product ring). Its kernel on G is normal and misses e_12(1), so it is trivial. Hence each nontrivial word is
   eventually nontrivial.

CLAIM "Proof of thm:main" (keys 879174153d4e … b596b717a720) → the absorbed `FiniteModelsAsymptotic.lean`, adapted to the tip:
printed φ_ℓ = 0 off radius ℓ, eventually additive and multiplicative, φ_ℓ(1) = I, as an `IsMatricialVia` producer for the
subshift ring. A new module GroupApproximation/Manuscript/SimpleKazhdanSofic/PeriodicMatrixUnits.lean covers "the shifts T^t y_ℓ are distinct, so products of P^iD_ℓ(e_a)P^{-i}
give every diagonal matrix unit, and with P every matrix unit". Ring generation (`1dd960096ceb`) is ct-involution's landed
`RingGeneration.subring_closure_eq_top`.

- MSI master down at ~00:00: `/tmp/msi-login.sock` is missing. Authoring continues; probes wait.

## 08:2x resume: infrastructure wiped (laptop reboot); offline authoring per main's broadcast

Origin/main is intact (tip f607305eb). The note tip is 696c4b602, unchanged in l.211–271 since 37551fd93. The census is still
at 37551fd93. nm/ infrastructure is gone, so no probes and no landings until main rebuilds it.

Target spellings (ct-two-ended, attic b44b743cc and 81bcaa7e4; names final):
- `IsMatricialVia S N φ`, now with `(∀ k, 0 < N k)`: my N_k = 0 counterexample is adopted;
- `PrintedMatricialMarkedLimitStatement`;
- `PrintedPeriodicMatricialStatement` over `printedGenerators S := insert 1 (ringGenerators_finite S).toFinset`, in `MainFromGeneral`;
- `PrintedBlockElementarySimple` is closed by ct-two-ended and the expanders by oa-expanders, so both are off my list.

CLAIM (added) GroupApproximation/Manuscript/SimpleKazhdanSofic/MatricialMarkedLimitWords.lean: char 2 from simplicity, π and ρ_k on
the letters, `isMarkedLimit_of_matricial` for every n ≥ 3. This is the producer of `PrintedMatricialMarkedLimitStatement` once
GeneralTheorem lands.
CLAIM (added) GroupApproximation/Manuscript/SimpleKazhdanSofic/SubshiftMatricial.lean: the printed cutoff φ_ℓ, φ_ℓ(1) = I,
φ_ℓ(u^j) = P^j, φ_ℓ(e_a) = diag(1_{y_ℓ(t)=a}), distinct translates from the least period, generation, eventual additivity and
multiplicativity, reindexing to `Fin`. `exists_periodicMatricial` is the body of `PrintedPeriodicMatricialStatement`.

Offline drafts, none probed yet (md5, with backups in the session scratchpad):
| module | md5 | contents |
|---|---|---|
| MatricialMarkedLimit | f3c8f8e2 | root-marking generation, φ∘π = ρ eventually, trivial ⇒ eventually trivial, ultraproduct RingCon and ring hom, trivial kernel |
| MatricialMarkedLimitWords | 18d6f2b0 | char 2, π/ρ letters, `isMarkedLimit_of_matricial` |
| PeriodicMatrixUnits | a4886c21 | P^i in the closure, conjugation, diagonal units, all matrix units, closure = ⊤, transport through a ring equiv |
| SubshiftMatricial | 4cb6548e | cutoff model, letters, distinct translates, `exists_periodicMatricial` |
| FiniteModelsAsymptotic (absorbed) | c2f943d5 | ms-units' `AsymptoticModels`; both earlier probes red, errors unread |

Probe order once infrastructure returns: MatricialMarkedLimit + MatricialMarkedLimitWords, then FiniteModelsAsymptotic +
PeriodicMatrixUnits + SubshiftMatricial.

CLAIM (added) GroupApproximation/Manuscript/SimpleKazhdanSofic/MatricialEndpoints.lean (path free on disk and origin; no other
producer). It holds the closed `printedMatricialMarkedLimitStatement` and `printedPeriodicMatricialStatement` over ct-two-ended's
`GeneralTheorem` and `MainFromGeneral` (unlanded), from `isMarkedLimit_of_matricial` and `exists_periodicMatricial`. Draft md5
4ebf330e, backed up; not probed. Land after ct-two-ended's two modules, and co-probe with them.

## 08:37 INFRA READY (NM in this session's scratchpad; clone cs-limit). Census regenerated at the tip 696c4b602 (aa6f988f4).
- Rows re-keyed: `e4fd510a51c5` formalized (printedBlockElementarySpecialLinear). Dropped `13bf024677ad` and `414df07890f1`, which are
  gone from the census.
- Step 1: co-probe MatricialMarkedLimit + MatricialMarkedLimitWords, running.
- 08:4x step 1 LANDED on real BUILT lines, with clean axioms: MatricialMarkedLimit 8e8cd3c9b (probe 0914-084124-91576) and
  MatricialMarkedLimitWords 77d39b591 (probe 0914-084424-82738). Both are queued for wiring.
- Rows added (Finite simple models):
  - formalized: a339b883c9d3, db0ff25cc298, 3d7e4722fef8, 9a9aa9313dca;
  - definition: 25fefb1e2ac1;
  - partial: 2e17cbfab2b6, cbc0b3980a99, d228d6575111, 995620260311.
- Step 2 probing: FiniteModelsAsymptotic + PeriodicMatrixUnits + SubshiftMatricial.
- 08:5x absorbed ms-units rows re-keyed and landed at 5474eded0 (`metadata/sk-census-rows/ms-units.tsv`): 3 kept, 11 stale keys
  dropped, 5 added. Of those, `2ffe206d32dd`, `63b955601626`, `e0aae9c0b4eb` and `72e70d46a29f` are partial (uncentered carriers against
  the printed centered windows), and `c1b8b83f890d` is a definition.
- ct-two-ended's `GeneralTheorem` is on origin at 40cf3ae5b; its spellings of `IsMatricialVia` (with `0 < N k`), the markings and
  `PrintedMatricialMarkedLimitStatement` are verified unchanged. `MainFromGeneral` is not yet on origin.

CLAIM GroupApproximation/Manuscript/SimpleKazhdanSofic/MatricialMarkedLimitEndpoint.lean (path free on disk and origin; no other
producer): the closed `printedMatricialMarkedLimitStatement`, imports GeneralTheorem + MatricialMarkedLimitWords. It is split
out of `MatricialEndpoints`, which now holds only `printedPeriodicMatricialStatement` (waiting on MainFromGeneral and step 2).
Probe after step 2 finishes.
- Step 2 re-probe after two fixes: `RingHom.map_closure`, and dropping the unused "eventually nonzero" clause from
  `AsymptoticModels`, since the tip's route gets nontriviality from the ultraproduct kernel.
- 09:0x step 2 LANDED on real BUILT lines, with clean axioms:
  - FiniteModelsAsymptotic 53bc26431 (probe 0914-084921-6784);
  - PeriodicMatrixUnits + MatricialMarkedLimitEndpoint 4d1ec38cf (probe 0914-085418-11178);
  - SubshiftMatricial 88e392873 (probe 0914-090006-2838).
- 09:1x step 3 LANDED MatricialEndpoints a1c4c8ca5 (probe 0914-090512-83787). **Both residual pieces of thm:general and thm:main are closed:**
  `printedMatricialMarkedLimitStatement` (4d1ec38cf) and `printedPeriodicMatricialStatement` (a1c4c8ca5). Every module is queued for
  wiring; ct-two-ended and main were told.
- The note moved to f34e9c0b1 (09:05); the census is still at 696c4b602. Rows were keyed only for sentences verified at the tip.
  - Proof of thm:main rows added: 879174153d4e, 1dd960096ceb, 6c900cb94747, 769f446cc3f5 formalized; 46b4acb4ea4f, fca8bece2919 definition;
    b596b717a720 partial. The absorbed a62656a98556 is upgraded to formalized.
  - Changed at the tip, to re-key at the next census:
    - skipped: ;
    - my landed rows: ;
    - absorbed rows: .

## 09:2x next item (main): printed-route carriers for the route-difference partial rows

All seven sentences were verified verbatim at tip f34e9c0b1; the census is still at 696c4b602 (skf-census is regenerating).

CLAIM GroupApproximation/Manuscript/SimpleKazhdanSofic/PeriodicWordCentered.lean: the proof of thm:main with centered windows as
printed.
- `2ffe206d32dd`: the forward orbit is dense, every word occurs in x_{[0,∞)}, and x_{[−ℓ,ℓ]} recurs at arbitrarily large positions.
- `63b955601626`: m with x_{[m−ℓ,m+ℓ]} = x_{[−ℓ,ℓ]} and every (2ℓ+1)-word occurring in x_{[0,m)}.
- `e0aae9c0b4eb`: y_ℓ = x on [−ℓ, m+ℓ].
- `72e70d46a29f`: every window is a translate of one centered in [0,m), so y_ℓ has the same words.

CLAIM GroupApproximation/Manuscript/SimpleKazhdanSofic/MatricialMarkedLimitDegree.lean: "Finite simple models" as printed.
- `2e17cbfab2b6`: π and ρ_k are onto, so both elementary maps from EL_n(F) are onto.
- `cbc0b3980a99`: EL_n(F) is generated by e_ij(1) and e_ij(τ_s), and e_ij(τ_1) has the same image as e_ij(1).
- `d228d6575111`: the degree filtration spanned by monomials of length ≤ λ; entries of words of length ≤ λ lie in it; it is finite for
  finite S; φ_k∘π = ρ_k uniformly on it for large k.

## 10:0x resume after the ~09:36 API/DNS outage (census 9cb80166d at tip 8b36733d7)

- Reconciled: nothing half-landed; the last landing is the claim b66331dae. PeriodicWordCentered is fixed (`lt_or_ge`,
  `Int.add_mul_emod_self_left`) and co-probing with MatricialMarkedLimitDegree.

CLAIM row `4d2e3277d31f` (l.240–242, rekeyed topological freeness): "Minimality and infiniteness imply that X has no isolated points and
T has no periodic points, so X is a Cantor set and the action is topologically free." LANDED with this commit as formalized over the
landed carriers `perfectSpace_carrier`, `isTopologicallyFree_shift` (ct-two-ended), `compactSpace_carrier`, and `zpow_apply_ne_self`
(ct-involution). `isTopologicallyFree_shift`'s body is `IsTopologicallyFreeAction` by definition.
- Absorbed row `6a7ff96154b3` (the LEF definition sentence) is dropped: it is gone from the census at the tip.
- 10:1x LANDED PeriodicWordCentered c9c59ce5c (probe 0914-100430-29409 BUILT; all four `#audit_closed_axioms` clean), queued for wiring.
  Rows flipped partial → formalized at 190eb60a9 (`metadata/sk-census-rows/ms-units.tsv`), each over its closed printed endpoint:
  - `2ffe206d32dd` over `printedCenteredRecurrence`;
  - `63b955601626` over `printedCenteredOccurrences`;
  - `e0aae9c0b4eb` over `printedPeriodicAgreesCentered`;
  - `72e70d46a29f` over `printedCenteredWindowsSameWords`.
- MatricialMarkedLimitDegree: probe 0914-100430-29409 red on four errors (unused section instances, `List.ofFn` composition, and a
  missing `DecidableEq` on the marking index for `FreeGroup.toWord`). All are fixed and in re-probe; `PrintedWordEntriesDegreeAgreement`
  now carries `[DecidableEq R]`. Rows `2e17cbfab2b6`, `cbc0b3980a99` and `d228d6575111` flip after it lands.
- 10:4x LANDED MatricialMarkedLimitDegree b10d07776 (probe 0914-104040-16720 BUILT; three `#audit_closed_axioms` clean), queued for wiring.
  Rows flipped partial → formalized, each over its closed printed endpoint:
  - `2e17cbfab2b6` over `printedLettersOntoQuotients`;
  - `cbc0b3980a99` over `printedFreeMarkingGeneration`;
  - `d228d6575111` over `printedWordEntriesDegreeAgreement`.
  **All seven route-difference partial rows are now formalized along the printed route.**
- 11:59 CLAIM the two remaining partial rows:
  - `995620260311` (tex 231–233: convergence, "G is LEF", N_k → ∞);
  - `b596b717a720` (tex 270–271: "φ_ℓ(S) generates M_{N_ℓ}(F₂), and Theorem thm:general applies").
  For each, name the open binder or the landed carrier that closes it, then flip the row or build the missing piece along the printed route.
