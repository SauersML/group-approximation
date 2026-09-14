# skf-cite: citation ledger, Questions, origin and bibliography of `simple_kazhdan_sofic_group.tex`

Lane skf-cite, 2026-09-13 ~21:40 CDT, under the 19:45 protocol and the 21:22 tip section of ct/ROSTER-sk.md.

## Target text

- origin/main note at 9047d0d3c (20:31, "Characterize LEF groups as subgroups of simple Kazhdan LEF groups"): 618
  lines, md5 274f19367f7f706b05c017af721c3884. skf-census regenerated the census at 9047d0d3c (d11e91f6e).
- Superseded: the ledgers at e80dcf20a (6eb502ac0, bb79d09bf) and at bf961c128 (8e3549247).
- Line numbers are at 9047d0d3c and for reading only; rows key by hash.

## Rows

`metadata/sk-census-rows/skf-cite.tsv` has 12 rows at the 9047d0d3c census. They cover:
- the Questions section and origin and authorship;
- the Pestov / Elek–Szabó sentence assigned by main;
- the one credit-only citation in Word problems that no range lane rows.

Changes from the e80dcf20a rows:
- **Dropped as duplicates of ms-intro-3's introduction rows:** `5c1db38e8d0c`, `b1eef5e651ae`, `30dcdf15b13a`,
  `870306a8de13` and `858f409740bb` (same grades), and `bf137432ddb7`. ms-intro-3 grades that one open, and the
  Stepanov route belongs to sk-stepanov. The new introduction sentences `3e190ace28f6` and `544404c03971` are left to
  ms-intro-3.
- **Dropped because the sentence changed:** `a036174dadc8`, `25a54a9f1b31`, `26e9baa90d07` and the unlanded
  `b565e2b44061`. Their successors are `544404c03971`, `585c79b57ae3`, `3606856b9a07` and `89a5cc12fe75`.
- **Declaration name corrected:** the earlier rows named
  `GroupApproximation.not_isResiduallyFinite_of_isSimpleGroup_of_infinite`. The declaration is
  `GroupApproximation.NinetyNineProblems.not_isResiduallyFinite_of_isSimpleGroup_of_infinite`, and the rows now name the
  closed `SimpleKazhdanSofic.printedInfiniteSimpleICCNotResiduallyFinite`.

## Claim done: LEF groups are sofic, and sofic groups are hyperlinear (tex l.185–186, census `89a5cc12fe75`)

- **Module:** `GroupApproximation/Manuscript/SimpleKazhdanSofic/LEFSoficHyperlinear.lean`, on main since dcad46f3c. A
  normal re-landing found the bytes identical.
- **Closed Props:** `PrintedLEFGroupsAreSofic`, `PrintedSoficGroupsAreHyperlinear` and
  `PrintedLEFSoficHyperlinearSentence`. All three `#audit_closed_axioms` report `[propext, Classical.choice, Quot.sound]`.
- **Evidence:**
  - BUILT at probe 0913-203054-6752. Its summary was lost to an MSI master drop, so it was read from the remote build
    log, including the three audit lines.
  - Compiled record 0913-203522-46221: a cache restore of the same bytes, md5 b53a3a3d….
- **Definitions against the printed notions:**
  - LEF (tex l.131–133) is `IsTextbookLEF`, equivalent to `IsLEF` by `isLEF_iff_textbook`.
  - `IsSofic` and `IsHyperlinear` are the finitary local forms. They are equivalent to the product-restricted
    conventions by `isSofic_iff_productRestricted` and `isHyperlinear_iff_productRestricted`.
  - Pestov's Definition 3.1 is the metric-ultraproduct form. The repository has no Lean equivalence with it.
- **Root reachability:** the carriers `isSofic_of_isLEF` and `isHyperlinear_of_isSofic` are root-direct. The new module is
  not root-wired, and neither is any other `SimpleKazhdanSofic` module; the lead wires them.
- **Wording:** at 9047d0d3c the citation for the second clause changed from Pestov Theorem 3.3 to Elek–Szabó Theorem 2.
  The mathematics is unchanged. The module docstring still quotes the e80dcf20a wording.

## Citations used as proof steps

| lines | cite | step | carrier on origin | verdict, owner |
|---|---|---|---|---|
| 124–127, 180–181, 304–307 | EJZ Thm 1.1 | EL_n of a finitely generated associative unital ring has (T), n ≥ 3; used for R, F and LC(Z,F₂) ⋊ L | `ejz` (FullDefectRingEJZUnconditional:46, closed audit); `printedElementaryPropertyT`, `printedFreeAlgebraElementaryKazhdan` | PROVED; the L instance is sk-lef-action's |
| 145–147 | Morse–Hedlund 1938 | a subshift with boundedly many words of each length is finite | none found by grep | ASSUMED; Finite models lanes (ms-units, ms-core-3) |
| 180–182 | Margulis, Kassabov | the finite quotients of the Kazhdan group EL_3(F) form expanders | none; `PrintedMarkedLimitExpandersStatement` is only a hypothesis of `printedSimpleKazhdanSoficMain_of_pieces` | ASSUMED; oa-expanders |
| 185–186 | Pestov Ex 4.5; Elek–Szabó Thm 2 | LEF ⇒ sofic; sofic ⇒ hyperlinear | `LEFSoficHyperlinear` (above) | PROVED, module not root-wired |
| 255–256 | Ozawa Prop 7.1 | hyperlinear ⇒ L(G) ↪ R^ω | none | ASSUMED; oa-ozawa71 over oa-hyperfinite and oa-ultrapower |
| 258–260 | McDuff | L(G) ⊗̄ R is a McDuff factor that embeds in R^ω, with G in its unitary group | ICC, not RF and II₁ factor are closed (`printedInfiniteSimpleICCNotResiduallyFinite`, `printedInfiniteSimpleGroupVonNeumannIIOneFactor`); the McDuff part has none | ASSUMED (McDuff part); oa-mcduff, oa-vn-tensor |
| 261–263 | Kirchberg Thm 1.1 | a Kazhdan group with the factorization property is RF | only through the binder `KirchbergKazhdanFactorizationInput` (NinetyNineProblems/FactorizationProperty) | ASSUMED; oa-kirchberg, oa-cstar-group |
| 263–265 | Ozawa p.527 | C*(G) fails the local lifting property | none | ASSUMED; oa-llp, oa-ucp |
| 288–290 | Ore Thm 1 | every even permutation of a finite set is a commutator of two permutations | none found by grep | ASSUMED; sk-ore |
| 355–356 | Malcev (no `\cite`, no bibliography entry) | finitely generated linear groups are residually finite | partial: `residuallyFinite_of_fg` (Algebra/MalcevLinear.lean:191), for a finitely generated subgroup of GL_d over a field, with binders | ASSUMED as printed; sk-malcev |
| 357–359 | Wilson Thm A | every countable RF group embeds in a 2-generator RF group | none found by grep | ASSUMED; sk-wilson |
| 382–386 | Morse–Hedlund, Hedlund 1944, Lothaire Ch. 2 | X_α is an infinite minimal subshift, the closure of the codings | `printedSturmianSubshiftInfiniteMinimal`, `printedSturmianSubshiftClosureOfCodings` (SturmianSubshiftMinimal:363–364, closed audits) | PROVED (skf-approximants, c04293088) |
| 408 | Vershik–Gordon | a finitely presented LEF group is RF | `printedFinitelyPresentedLEFResiduallyFinite` (QuestionsNotFinitelyPresented:121, closed audit) | PROVED (ms-compress-4, 16d890864) |

## Citations that are credit, context or questions

- 48 Brown, 49 Ozawa p.527, 50 Pestov: the question and its forms.
- 51–52 Rădulescu, Gromov, Weiss: who named or introduced hyperlinear and sofic groups.
- 71 Kazhdan: introduced property (T). 72 EJZ: introduction credit.
- 75 GM Thm 2.6 and 76 Kassabov: introduction credit.
- 76–79 Stepanov Thm 4.4: an alternative simplicity route that the direct proof does not use. The dimension-count lemma
  is unproved (sk-stepanov).
- 85 Matui, 87 Thom: context.
- 131 Vershik–Gordon: credit for the LEF definition.
- 178–180 Grigorchuk, Champetier: credit for the space of marked groups. The convergence itself is proved in the text
  and belongs to the Finite models lanes.
- 269–272 Gorjuskin, Schupp, Kionke–Schesler Thm 1.2: earlier embedding theorems, context. sk-lef-assembly rows them.
- 404 GMpres Thm 1.1(3): context.
- 411 Caprace–Rémy: finitely presented infinite simple Kazhdan groups exist; cited context for the question.
- 413 Alekseev–Thom, 420 GPS: inside questions.
- 419 GPS99, Bezuglyi–Medynets: the converse for topological full groups; context.

## Questions section (406–420)

| lines | census | sentence | grade | carrier or residual |
|---|---|---|---|---|
| 408–410 | `32a9f96774bd` | fp LEF ⇒ RF; G_X is not RF, so G_X is not finitely presented | partial | the general steps are closed (ms-compress-4); residual: the G_X instance, `printedGXNotFinitelyPresented_of_pieces` |
| 410–411 | `fdd05c47986c` | finitely presented infinite simple Kazhdan groups exist | attribution | cited context |
| 411–412 | `585c79b57ae3` | Is there one that is sofic, or at least hyperlinear? | open | a question |
| 412–415 | `3c8de4b91fec` | a positive answer would answer Alekseev–Thom Open problem 6.1 | partial | infinite simple ⇒ not RF is closed; see the wording note |
| 417–418 | `3606856b9a07` | conjugacy or flip conjugacy ⇒ G_X ≅ G_Y | partial | no carrier; ct-involution |
| 418–419 | `a5b818e4b8c5` | the converse holds for topological full groups | attribution | cited context |
| 419–420 | `34f8479b8e45` | Does G_X ≅ G_Y imply flip conjugacy, or strong orbit equivalence? | open | a question |

Wording note, still present at 9047d0d3c: only a sofic positive answer gives what Open problem 6.1 asks for. A
hyperlinear-only answer does not.

## Origin and authorship (422–426)

`5c45d7277fea`, `56609be15469`, `a51fe087e1a2`: attribution.

## Bibliography (428–616)

35 entries, each cited at least once: AlekseevThom, BezuglyiMedynets, Brown, CapraceRemy, Champetier, ElekSzabo, EJZ,
GPS, GPS99, Gorjuskin, Grigorchuk, GM, GMpres, Gromov, Hedlund44, Kassabov, Kazhdan, KionkeSchesler, Kirchberg,
Lothaire, Margulis, Matui, McDuff, MorseHedlund38, MorseHedlund, Ore, Ozawa, Pestov, Radulescu, Schupp, Stepanov, Thom,
VershikGordon, Weiss, Wilson. The census has no bibliography rows. Tex issue: Malcev's theorem (l.355) is used with no
citation and no bibliography entry.

## Cited results still assumed in the proof (9047d0d3c)

1. Morse–Hedlund 1938 (145–147): bounded complexity ⇒ finite subshift. Owner: the Finite models lanes.
2. Margulis / Kassabov (180–182): expanders. Owner: oa-expanders.
3. Ozawa Prop 7.1 (255–256): L(G) ↪ R^ω. Owner: oa-ozawa71.
4. McDuff (258–260): L(G) ⊗̄ R is McDuff and embeds in R^ω. Owner: oa-mcduff.
5. Kirchberg Thm 1.1 (261–263): carried only through a binder. Owner: oa-kirchberg.
6. Ozawa p.527 (263–265): the local lifting property. Owner: oa-llp.
7. Ore Thm 1 (288–290). Owner: sk-ore.
8. Malcev (355–356): partial carrier `MalcevLinear.residuallyFinite_of_fg`. Owner: sk-malcev.
9. Wilson Thm A (357–359). Owner: sk-wilson.
10. Stepanov Thm 4.4 (76–79): alternative route only. Owner: sk-stepanov.

Proved: EJZ Thm 1.1; Pestov Ex 4.5 and Elek–Szabó Thm 2 (`LEFSoficHyperlinear`); the Sturmian step (Morse–Hedlund,
Hedlund, Lothaire); Vershik–Gordon fp LEF ⇒ RF.

Correction: the 20:0x list sent to main still counted Morse–Hedlund (the Sturmian step) as assumed.
skf-approximants had landed closed carriers at 19:56 (c04293088), and my sweep had reused an older grep.
