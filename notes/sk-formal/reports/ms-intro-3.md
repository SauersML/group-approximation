# Lane ms-intro-3: `simple_kazhdan_sofic_group.tex` 1–66 at bf961c128 (abstract, introduction, thm:main)

Lead: session nonsofic-existence-49 (ROSTER-sk, re-scoped 18:58). Target text: origin/main bf961c128, 340 lines,
md5 7b3dc4ec92b4581553bc0dc2b0edcb99. Rows are keyed `LINE:<l>@bf961c128`. Nothing here is keyed to b965d63ba.

## Ledger v1

| l. | sentence (abridged) | grade | carrier / owner | verdict |
|---|---|---|---|---|
| 22 | title: An infinite simple Kazhdan sofic group | structural | — | title |
| 25 | subjclass | structural | — | metadata |
| 28–30 | For every infinite minimal subshift X, EL_3(LC(X,F_2)⋊Z) is infinite, simple, f.g., and has (T). | to be formalized | `PrintedSimpleKazhdanSoficMain` (this lane, CLAIM below) | GAP: see "Carriers on origin" |
| 30–31 | It is LEF, hence sofic and hyperlinear. | to be formalized | same | GAP |
| 31–32 | This answers the questions of Brown, Ozawa, and Pestov. | to be formalized | this lane: an existence statement through G_X; Palomar `exists_infinite_simple_propertyT_{hyperlinear,sofic}` answers them through the Toeplitz witness only | GAP for "these groups" |
| 32–33 | The proof combines periodic approximation with a commutator supported on a finite tower. | structural | roadmap of 118–153 (ms-units) and 174–228 (ct-bilateral-mf) | roadmap |
| 33–34 | Every Turing degree occurs as the word-problem degree of one of these groups. | partial until carried | skf-degrees' corollary (tex 231) | owner skf-degrees |
| 38 | Can an infinite simple Kazhdan group be hyperlinear? | structural | — | question |
| 38–40 | Brown asked this in its von Neumann algebra form in 2001, and Ozawa in the hyperlinear form in 2003. | attribution | Palomar/Pestov91Challenge.lean quotes both verbatim | attribution |
| 41 | Pestov's Open question 9.1 adds the sofic version. | attribution | same | attribution |
| 42 | The following construction answers both forms positively. | to be formalized | same carrier as 31–32 | GAP |
| 45–52 | thm:main: X ⊆ A^Z infinite minimal subshift over a finite alphabet, shift T; G_X = EL_3(LC(X,F_2)⋊_T Z) is infinite, f.g., simple, Kazhdan, LEF; in particular sofic and hyperlinear. | to be formalized | `PrintedSimpleKazhdanSoficMain` | GAP |
| 55 | The subshift algebra is classical; see Nekrashevych. | attribution | — | attribution |
| 56 | Property (T) is supplied by Ershov–Jaikin-Zapirain. | attribution | the cited theorem is proved: `Pestov91.elementary_hasKazhdanPropertyT` via `IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT` | attribution, input proved |
| 57–58 | Our finite models use the periodic-approximation mechanism of Grigorchuk–Medynets. | attribution | route carrier with ms-units (118–153) | attribution |
| 58–61 | The new step is the simplicity argument: a nontrivial normal subgroup meets a finite simple matrix group supported on a clopen tower, and therefore contains an elementary matrix. | partial until carried | tower clause: ct-bilateral-mf (174–228); conclusion "contains an elementary matrix": this lane, from the tower carrier | owner ct-bilateral-mf for the tower |
| 61–62 | This is an explicit elementary-matrix extraction argument, in the normal-structure tradition described by Stepanov. | attribution | — | attribution |
| 63–65 | Thom had already constructed a f.g. Kazhdan LEF group that is not residually finite; his example is not simple. | attribution | — | prior work |

## Carriers on origin (checked at origin ~19:05)

- The Palomar Pestov 9.1 endpoint (`Pestov91.exists_infinite_simple_kazhdan_lef`, WitnessAssembly) is the Toeplitz subshift
  only, and its group is EL_3(A)/Z; it does not state thm:main at every infinite minimal subshift.
- General pieces that exist for any compact totally separated X with a free minimal Z-action:
  - `Pestov91.isSimpleGroup_elementaryModCentre_of_minimal_free` and `Pestov91.isSimpleRing_of_minimal_free`, for any ring R
    with `φ : LC(X,K) →+* R`, a unit `u`, conjugation and spanning;
  - `Pestov91.central_zero_or_one_of_free_minimal` (over F_2) and `Pestov91.center_elementaryGroup_eq_bot_of_central_zero_or_one`,
    so Z(G) = 1 and EL_3 itself is simple;
  - `Pestov91.elementary_hasKazhdanPropertyT` (EJZ, proved), `Sofic.isSofic_of_isLEF`, `Pestov91.isHyperlinear_of_isLEF`,
    `Pestov91.isLEF_elementaryGroup`.
- Chain-core ring: `ClopenCrossedProduct T k` has `u f u⁻¹ = f ∘ T⁻¹`, the printed convention.
- Missing for every infinite minimal subshift: the subshift and minimality vocabulary on A^Z, freeness from minimal plus
  infinite (tex 78, ct-involution's range), finite generation by u^{±1} and the letter indicators (tex 84–86, ct-involution),
  and LEF of R_X (tex 118–153, ms-units).

## Claims

- CLAIM the thm:main statement and its assembly over named piece statements —
  `GroupApproximation/Manuscript/SimpleKazhdanSofic/MainTheorem.lean`. The path is free on origin, in the shared tree and in
  every `lanes/*.files` (checked ~19:05). The pieces owned by other lanes are consumed as named Props, and their owners are
  recorded here.

## Progress log

- 19:05 ledger v1 at bf961c128.
