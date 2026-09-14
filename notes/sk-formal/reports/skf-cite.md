# skf-cite: citation sweep, Questions, origin and bibliography of `simple_kazhdan_sofic_group.tex`

Lane skf-cite, 2026-09-13 ~19:55 CDT, under the 19:45 protocol of ct/ROSTER-sk.md.

## Target text

- origin/main note at e80dcf20a (19:39, "Show the simple Kazhdan groups are marked limits of finite simple expanders"):
  386 lines, md5 4ad4921253626a4f858866c716a13385. Origin tip at sweep time: bcd92d639.
- The earlier ledger (8e3549247) was at bf961c128 and is superseded; the note was rewritten three times since
  (5b1890ce6, 2050a8eed, e80dcf20a).
- Line numbers below are at e80dcf20a. They are for reading only: rows key by hash.
- `metadata/SK_SENTENCE_CENSUS.tsv` on origin is still at bf961c128 (77af1c5ea). skf-census has been asked to regenerate it
  at the tip, and rows wait for it, except sentences verified verbatim at the tip.

## Citations used as proof steps

| lines | cite | step | Lean carrier (origin/main) | verdict |
|---|---|---|---|---|
| 110–113 | EJZ Thm 1.1 | EL_n(S) has (T) for every finitely generated associative unital ring S, n ≥ 3. Used for R (l.113) and for the free algebra F (l.163). | `ejz : FinitelyGeneratedRingGeneralRankElementaryPropertyT` (Manuscript/OneSidedMFRadical/FullDefectRingEJZUnconditional.lean:46, `#audit_closed_axioms` l.154), via `IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT`. Root-direct. | PROVED |
| 163–164 | Kassabov | Since EL_3(F) has (T), the Cayley graphs of its finite quotients SL_{3N}(F₂), with the images of a fixed generating set, form expanders. | NONE. Origin has no "finite quotients of a Kazhdan group are expanders" lemma; `ExpanderDecomposition` and `IsEssentialExpanderSequence` (Criterion, Kun) are different objects. | ASSUMED, GAP (Finite models: ms-units, ms-core-3) |
| 164–166 | Pestov Ex 4.5, Thm 3.3 | LEF ⇒ sofic ⇒ hyperlinear | `isSofic_of_isLEF` (Sofic/LEFSofic.lean:85), `isHyperlinear_of_isSofic` (Sofic/Hyperlinear.lean:175). Root-direct. Neither module has an `#audit` line. | PROVED provisionally; axiom audit owed |
| 168 | Ozawa Prop 7.1 | G hyperlinear ⇒ L(G) embeds in R^ω | NONE. No R^ω, II₁-factor or von Neumann algebra carrier on origin; `IsHyperlinear` (Sofic/Hyperlinear.lean:154) is the unitary-approximation form. | ASSUMED, GAP (Finite models) |
| 173–176 | Kirchberg Thm 1.1 | A Kazhdan group with the factorization property is residually finite; so G lacks the factorization property | `not_hasFactorizationProperty_of_isSimpleGroup_of_infinite_of_kazhdan` (Manuscript/NinetyNineProblems/FactorizationProperty.lean:203) takes the leading binder `k : KirchbergKazhdanFactorizationInput`, which stands for Kirchberg's theorem. `HasFactorizationProperty` (l.119) is the trace-side definition; its equivalence with the tensor-norm definition (Brown, Mem. AMS 184, Thm 4.1.9) is "cited, not proved here". | ASSUMED (literature binder), GAP (Finite models) |
| 176–177 | Ozawa p.527 | C*(G) does not have the local lifting property | NONE. `NuclearQuotient.CPCLocalLiftingInput` is a different Prop. | ASSUMED, GAP (Finite models) |
| 261–264 | Morse–Hedlund | X_α, the closure of the codings c(θ), is an infinite minimal subshift | NONE; no Sturmian carrier on origin. | ASSUMED, GAP (Word problems: skf-approximants) |
| 281 | Vershik–Gordon | A finitely presented LEF group is residually finite | `finitelyPresented_isLEF_residuallyFinite` (Sofic/FinitelyPresentedLEF.lean:25): every nontrivial element of a group presented by a finite relator set survives in a finite symmetric group. Root-direct; `#audit_axioms` at Endpoint/Audit.lean:349. | PROVED |

## Citations that are credit, context or questions

- 43 Brown, 44 Ozawa, 45 Pestov: the question and its forms.
- 65 EJZ, 67 Grigorchuk–Medynets Thm 2.6, 68 Kassabov: introduction credit. The note proves its finite models directly at
  121–163.
- 77 Matui, 79 Thom, 249 GMpres Thm 1.1(3): context.
- 286 Alekseev–Thom and 291 GPS: citations inside the Questions section.
- 117 Vershik–Gordon credits the LEF definition, whose carrier is `Sofic.IsLEF`; that row belongs to the Finite models
  lanes.
- 69–72 Stepanov Thm 4.4: an alternative simplicity route. The sentence also asserts that any p, q ∈ R satisfy pr + qs = 0
  with (r,s) ≠ 0, "by a dimension count on one cylinder". Neither Stepanov 4.4 nor that lemma has a carrier. The direct
  proof at 179–237 carries simplicity, so this is a remark row: partial, residual Stepanov Thm 4.4 plus the dimension-count
  lemma (Introduction: ms-intro-3).

## Carrier-less steps near citations (no citation, noted for owners)

- 169–173 (Finite models): G infinite simple ⇒ its nontrivial conjugacy classes are infinite; L(G) is a II₁ factor;
  L(G) ⊗̄ R is a McDuff factor that embeds in R^ω, with G in its unitary group. No von Neumann algebra carriers.
- 282: "the infinite simple group G_X is not residually finite" is `not_isResiduallyFinite_of_isSimpleGroup_of_infinite`
  (FactorizationProperty.lean:175). The proof has no binder, the module is root-direct, and it has `#audit_axioms`.

## Questions section (279–292)

| lines | sentence | grade | carrier / residual |
|---|---|---|---|
| 281–283 | fp LEF ⇒ RF; G_X is not RF, so G_X is not finitely presented | partial | `finitelyPresented_isLEF_residuallyFinite`, `not_isResiduallyFinite_of_isSimpleGroup_of_infinite`. Residuals: G_X LEF (Finite models) and the transfer from a finitely presented group to `PresentedGroup` over a finite relator set. |
| 283–284 | Is there a finitely presented infinite simple group with (T) that is sofic, or at least hyperlinear? | open | a question |
| 284–287 | A positive answer would also answer Open problem 6.1 of Alekseev–Thom (fp sofic (T) groups that are not RF) | partial | carrier `not_isResiduallyFinite_of_isSimpleGroup_of_infinite`. Wording note: only the sofic form of a positive answer gives an fp sofic (T) non-RF group; a hyperlinear-only answer would not answer 6.1. |
| 289–290 | If (X,T) is conjugate to (Y,S) or (Y,S⁻¹), then G_X ≅ G_Y | partial | NO carrier. Residual: a ring isomorphism LC(X,F₂) ⋊_T ℤ ≅ LC(Y,F₂) ⋊_S ℤ from a conjugacy, and one via u ↦ u⁻¹ from a flip; then EL_3 of an isomorphism. |
| 290–291 | Does G_X ≅ G_Y imply flip conjugacy, or at least strong orbit equivalence? | open | a question |

## Origin and authorship (293–297)

- "Claude (Anthropic) found the construction and original proofs … and wrote the manuscript": attribution. Its text changed
  at 2050a8eed, so it waits for a regenerated hash.
- "The author is responsible for the final manuscript" (`56609be15469`) and "Proof records are in the project repository"
  (`a51fe087e1a2`): attribution. Both are verbatim at the tip, so their hashes still apply, and they are the only rows
  landed now.

## Bibliography (299–385)

15 entries: AlekseevThom, Brown, EJZ, GM, GMpres, GPS, Kassabov, Kirchberg, Matui, MorseHedlund, Ozawa, Pestov,
Stepanov, Thom, VershikGordon. The census has no bibliography rows.

## Cited results still assumed in the proof

1. Kassabov (163–164): finite quotients of a Kazhdan group form expanders.
2. Ozawa Prop 7.1 (168): hyperlinear ⇒ L(G) ↪ R^ω.
3. Kirchberg Thm 1.1 (173–176): only through the binder `KirchbergKazhdanFactorizationInput`.
4. Ozawa p.527 (176–177): C*(G) fails the local lifting property.
5. Morse–Hedlund (261–264): X_α is infinite and minimal.
6. Stepanov Thm 4.4 (69–72): the alternative simplicity route, including the dimension-count lemma.

Provisional: Pestov Ex 4.5 / Thm 3.3 (audit owed). Proved: EJZ Thm 1.1, Vershik–Gordon fp LEF ⇒ RF, infinite simple ⇒
not RF.
