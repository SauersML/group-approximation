# Lane ms-intro-3: `simple_kazhdan_sofic_group.tex`, abstract, introduction and thm:main statement

Lead: session nonsofic-existence-49 (ROSTER-sk, protocol 19:45). Target: the current origin/main tip of the note, 9047d0d3c
(20:31), 618 lines, md5 274f19367f7f706b05c017af721c3884. Rows are keyed by the 12-hex sentence hash from
`metadata/SK_SENTENCE_CENSUS.tsv`, and land only once skf-census has regenerated the census at the tip md5. At ~20:35 the census
on origin (09e580c38) is still at e80dcf20a, so the row update citing MainAssembly is held back by the md5 gate.

## Ledger v3 (tip 9047d0d3c)

| l. | sentence (abridged) | grade | carrier / owner | verdict |
|---|---|---|---|---|
| 23 | title | structural | — | title |
| 26–27 | subjclass, keywords | structural | — | metadata |
| 30–32 | For every infinite minimal subshift X, G_X is infinite, f.g., simple, with (T). | partial | `PrintedSimpleKazhdanSoficMain`, `printedSimpleKazhdanSoficMain_of_pieces` (ct-two-ended, LANDED bf15b32cf) | statement verified faithful |
| 32–34 | limit of finite simple SL_{3N}(F₂) in the space of marked groups, expander Cayley graphs | partial | `PrintedMarkedLimitExpanders`, `IsMarkedLimit`, `IsExpanderFamily` (same module) | verified faithful |
| 34–35 | So G_X is LEF, sofic and hyperlinear. | partial | same endpoint | verified |
| 35–37 | This answers the question of Brown and Ozawa ..., and Pestov's sofic version of it. | formalized (existence) / partial (G_X form) | this lane, `ToeplitzAnswer` (in flight): closed `printedBrownOzawaPestovAnswer`; `printedGXAnswersBrownOzawaPestov_of_main` at the Toeplitz subshift | see below |
| 37–40 | A f.g. group is LEF iff it is a subgroup of an infinite f.g. simple Kazhdan LEF group, and one such group contains every f.g. linear group. | open | restates cor:lef (l.276, section "LEF groups", l.267–362); owner not in the 19:45 roster table | NEW at 9047d0d3c; owner to be ruled |
| 40–41 | Every Turing degree is the word-problem degree of some G_X. | open | skf-degrees (section "Word problems") | owner skf-degrees |
| 45 | Can an infinite simple group with (T) be hyperlinear? | structural | — | question |
| 46–48 | Brown 2001, McDuff factor form | attribution | quoted verbatim in `Palomar/Pestov91Challenge.lean` | attribution |
| 49–50 | Ozawa 2003 hyperlinear form; Pestov 9.1 sofic form | attribution | same | attribution |
| 50–52 | Hyperlinear groups were named by Rădulescu; sofic groups were introduced by Gromov and named by Weiss. | attribution | — | NEW, prior work |
| 52–53 | The groups below answer all three forms positively. | partial | `ToeplitzAnswer` (Ozawa and Pestov forms); Brown's form is subsection "Brown's formulation" (l.254–266) | Brown form owner to be named |
| 55–68 | thm:main (every n ≥ 3) | partial | ct-two-ended's statement and assembly over four named pieces | verified faithful clause by clause |
| 71–72 | Property (T), introduced by Kazhdan, follows from Ershov–Jaikin-Zapirain. | attribution | cited theorem proved: `Pestov91.elementary_hasKazhdanPropertyT` | attribution, input proved |
| 72–76 | periodic approximation as in Grigorchuk–Medynets [Thm 2.6]; expanders as in Kassabov | attribution | route carriers with ms-units / ms-core-3 | attribution |
| 76–79 | Simplicity also follows from Stepanov's theorem, since ... pr+qs=0 with (r,s)≠0, by a dimension count on one cylinder. | owner sk-stepanov | sk-stepanov (lane OA 20:15). The dimension-count claim is true: my hand check was sent to sk-stepanov ~20:33 | not built here |
| 79–83 | Our proof is direct: a nontrivial normal subgroup contains ... an elementary matrix. | partial | `PrintedSimplicityStatement` (MainAssembly), owners ct-bilateral-mf / skf-consequences | roadmap |
| 83–85 | Matui [Lemma 3.4, Thm 4.9] | attribution | — | prior work |
| 85–87 | Thom's f.g. Kazhdan LEF not residually finite group is not simple. | attribution | — | prior work |
| 89–93 | The same proof applies to the lamplighter action of Δ on F₂^Δ; it shows the LEF characterization (cor:lef), and one such group contains every f.g. linear group. | open | cor:lef carriers; owner to be ruled | NEW at 9047d0d3c |

## thm:main (settled ~20:25)

- ct-two-ended landed the statement and the assembly in one module, `Manuscript/SimpleKazhdanSofic/MainAssembly.lean`
  (bf15b32cf, 20:24): `PrintedSimpleKazhdanSoficMain`, `PrintedMarkedLimitExpanders`, `IsMarkedLimit`, `IsExpanderFamily`, and
  `printedSimpleKazhdanSoficMain_of_pieces` over `PrintedSubshiftRingFGStatement`, `PrintedSimplicityStatement`,
  `PrintedMarkedLimitExpandersStatement` and `PrintedMarkedLimitLEFStatement`.
- Main's 20:15 note assigned the statement Prop to this lane, but it was already landed. A second Prop would collide, so this
  lane adopted it and verified it against tip l.55–68:
  - setting: A finite discrete, `Subshift A ℤ`, `Infinite S.carrier`, `IsMinimal S`, `R S = ClopenCrossedProduct (subshiftHomeo S) (ZMod 2)`;
  - infinite, f.g., simple, `HasKazhdanPropertyT`, for every n ≥ 3 over `elementaryGroup (Fin n) (R S)`, with n = 3 being G_X;
  - marked limit: simple `SpecialLinearGroup (Fin n × Fin (N ℓ)) (ZMod 2)`, generating families with common labels, and
    word-by-word eventual agreement;
  - expanders: finite labels, `Nat.card → ∞`, and a uniform ε edge-expansion bound for sets of at most half size;
  - LEF, sofic, hyperlinear.
  Main was told ~20:26.

## Landed and in flight

- LANDED f61392374: `Manuscript/SimpleKazhdanSofic/Setting.lean` (`subshiftHomeo`, `IsMinimal`, `letterIndicator`, `R`, `G`).
- LANDED 4da904291: `Manuscript/SimpleKazhdanSofic/MinimalDenseOrbits.lean` (`subshiftHomeo_zpow_apply`,
  `minimalSubshift_dense_orbits`).
- LANDED 08a723d3d: census rows at e80dcf20a. They must be re-keyed at the next census regeneration.
- In flight: `Manuscript/SimpleKazhdanSofic/ToeplitzAnswer.lean`.
  - `toeplitzSubshift : Subshift Bool ℤ` (carrier `Pestov91.subshiftCarrier`), `toeplitzSubshift_isMinimal`,
    `toeplitzSubshift_infinite`;
  - `printedBrownOzawaPestovAnswer : PrintedBrownOzawaPestovAnswer` (closed: some infinite simple Kazhdan group is sofic and
    hyperlinear), via `Pestov91.exists_infinite_simple_kazhdan_lef`;
  - `printedGXAnswersBrownOzawaPestov_of_main : PrintedSimpleKazhdanSoficMain → PrintedGXAnswersBrownOzawaPestov` (some G_X
    at an infinite minimal subshift), at the Toeplitz subshift.

## Progress log

- 19:05 ledger v1 at bf961c128 (superseded).
- 19:25 spelling settled on skf-degrees' `Subshift` vocabulary.
- 19:45 note at e80dcf20a; protocol by section and 12-hex keys.
- 19:55–20:05 split crossings with ct-two-ended; Setting and MinimalDenseOrbits landed; rows landed at e80dcf20a.
- 20:03 API outage; 20:15 resume.
- 20:25 adopted ct-two-ended's landed statement after verifying it; l.69–72 handed to sk-stepanov.
- 20:35 note at 9047d0d3c (new abstract sentence on the LEF characterization); ledger v3; ToeplitzAnswer probing.
