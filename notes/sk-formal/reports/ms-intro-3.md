# Lane ms-intro-3: `simple_kazhdan_sofic_group.tex`, abstract, introduction and thm:main statement

Lead: session nonsofic-existence-49 (ROSTER-sk, protocol 19:45). Target: the current origin/main tip of the note, e80dcf20a,
386 lines, md5 4ad4921253626a4f858866c716a13385. Ranges are by section. Rows are keyed by the 12-hex sentence hash from
`metadata/SK_SENTENCE_CENSUS.tsv`, and land only once skf-census has regenerated the census at this md5. At the time of writing
the census on origin (77af1c5ea) is still at bf961c128.

## Ledger v2 (tip e80dcf20a)

| l. | sentence (abridged) | grade | carrier / owner | verdict |
|---|---|---|---|---|
| 22 | title: Infinite simple Kazhdan groups that are limits of finite simple groups | structural | — | title |
| 25 | subjclass | structural | — | metadata |
| 28–30 | For every infinite minimal subshift X, G_X = EL_3(LC(X,F_2)⋊Z) is infinite, f.g., simple, with (T). | formalized once the endpoint lands | `PrintedSimpleKazhdanSoficMain`, ct-two-ended's `MainAssembly` | owner ct-two-ended |
| 30–32 | It is a limit of finite simple SL_{3N}(F_2) in the space of marked groups, and their Cayley graphs form a family of expanders. | same | `PrintedMarkedLimitExpanders` (ct-two-ended statement; producers ms-units / ms-core-3) | owner ct-two-ended |
| 32–33 | So G_X is LEF, sofic and hyperlinear. | same | same endpoint | owner ct-two-ended |
| 33–35 | This answers the question of Brown and Ozawa whether an infinite simple Kazhdan group can be hyperlinear, and Pestov's sofic version of it. | to be formalized | this lane: the existence statements of `Palomar/Pestov91Challenge.lean`, through G_X at a concrete infinite minimal subshift, from the thm:main endpoint | GAP (this lane) |
| 35–36 | Every Turing degree is the word-problem degree of some G_X. | formalized once carried | skf-degrees' corollary | owner skf-degrees |
| 40 | Can an infinite simple group with (T) be hyperlinear? | structural | — | question |
| 41–43 | Brown asked this in 2001 as a question about embeddings into unitary groups of McDuff factors that embed in R^ω. | attribution | quoted verbatim in `Palomar/Pestov91Challenge.lean` | attribution |
| 44–45 | Ozawa stated the hyperlinear form in 2003, and Pestov's Open question 9.1 adds the sofic form. | attribution | same | attribution |
| 45–46 | The groups below answer all three forms positively. | to be formalized | same carrier as 33–35 | GAP (this lane) |
| 48–62 | thm:main (every n ≥ 3: infinite, f.g., simple, (T), marked limit of SL_{nN}(F_2) with expander Cayley graphs, LEF, sofic, hyperlinear) | formalized once the endpoint lands | ct-two-ended's `PrintedSimpleKazhdanSoficMain` and closed theorem | owner ct-two-ended; census rows here |
| 64–65 | Property (T) follows from the theorem of Ershov and Jaikin-Zapirain. | attribution | cited theorem proved: `Pestov91.elementary_hasKazhdanPropertyT` | attribution, input proved |
| 65–68 | The finite models use periodic approximation, as in Grigorchuk–Medynets [Theorem 2.6], and the expanders arise as in Kassabov's construction. | attribution | route carriers with ms-units / ms-core-3 | attribution |
| 69–72 | Simplicity also follows from Stepanov's theorem [Theorem 4.4], since the ring is simple and any two of its elements p,q satisfy pr+qs=0 with (r,s)≠0, by a dimension count on one cylinder. | to be formalized | this lane: the cylinder dimension count for R; the consequence "simplicity follows from Stepanov" needs Stepanov 4.4 proved or is graded partial | GAP (this lane) |
| 72–75 | Our proof is direct: a nontrivial normal subgroup contains a nontrivial commutator lying in a copy of GL_d(F_2) over a clopen tower, so it contains this group and with it an elementary matrix. | partial until carried | the Simplicity section (ct-bilateral-mf, skf-consequences) | owner ct-bilateral-mf |
| 75–77 | For derived topological full groups, Matui showed in the same way that a nontrivial normal subgroup meets a simple union of alternating groups on towers. | attribution | — | prior work |
| 77–79 | Thom constructed a f.g. Kazhdan LEF group that is not residually finite, but his example is not simple. | attribution | — | prior work |

## Split of thm:main (settled with ct-two-ended ~20:05, after three crossed messages)

- ct-two-ended owns the statement `PrintedSimpleKazhdanSoficMain` (every n ≥ 3, with the marked-limit and expander clause)
  and its closed theorem, both in `Manuscript/SimpleKazhdanSofic/MainAssembly.lean`, along the printed tower route. This lane
  writes no MainStatement module.
- This lane owns the census rows of the abstract, introduction and thm:main statement (citing ct-two-ended's endpoint once it
  lands), the answer sentences 33–35 and 45–46, the cylinder dimension count at 69–72, Setting and MinimalDenseOrbits.
- My n = 3 draft `MainTheorem.lean` (Pestov91 free-minimal route) is retired. It was never landed; its text is at attic
  681714c37, and ct-two-ended may reuse pieces.

## Landed and in flight

- LANDED f61392374: `Manuscript/SimpleKazhdanSofic/Setting.lean`, queued for wiring. It holds `subshiftHomeo`, `IsMinimal`,
  `letterIndicator`, `R`, `G` over Mathlib's `Subshift A ℤ`, which is skf-degrees' spelling, adopted by ct-involution and
  ct-two-ended.
- In flight: `Manuscript/SimpleKazhdanSofic/MinimalDenseOrbits.lean`, with `subshiftHomeo_zpow_apply` and
  `minimalSubshift_dense_orbits : IsMinimal S → Dense (range fun j => (subshiftHomeo S ^ j) x)`.

## Progress log

- 19:05 ledger v1 at bf961c128 (superseded).
- 19:25 spelling settled on skf-degrees' `Subshift` vocabulary.
- 19:45 note at e80dcf20a; protocol by section and 12-hex keys.
- 19:55 split with ct-two-ended; Setting landed; ledger v2 at the tip.
