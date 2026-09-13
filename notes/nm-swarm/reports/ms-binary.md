# Lane ms-binary: "The binary example" and the opening of "MF quotients of unit groups"

Range: tex 1175–1231 at origin/main 68481e4d7. Snapshot: origin/main 61363f1b9 (2026-09-13). Census rows were matched by
text, because the census line numbers (1163–1205) are at the pre-chain-core manuscript hash.

Every sentence of the range has a census row. Every literature input the range uses is proved on main, not assumed:
- Khanh–Thanh Proposition 4.2 and Corollary 4.4;
- Ershov–Jaikin-Zapirain Theorem 1.1;
- Bekka–de la Harpe–Valette Theorem 1.3.1;
- Abrams–Aranda;
- Ara's exchange theorem;
- Preusser Theorem 3;
- Aranda–Crow Corollary 4.3;
- Whitehead's lemma.

Tex line 87 defines MF only for countable groups, so `IsCDEOperatorMF M` with `[Countable M]` is the printed generality.

## Ledger

| key | status | sentence | verdict |
|---|---|---|---|
| 2ff180315a15 | definition | Put R = L_{F_2}(1,2) and H = R^×. | OK: `RankFourEndpoint.R`, `BinaryExampleUnitGroup` |
| 98115b8e2580 | formalized | the right-module maps R ≅ R ⊕ R, and H ≅ GL_4(R) = EL_4(R) [KhanhThanh] | OK: `manuscriptSentence_leavittModuleEquivProd` (inverse maps, additive, right linear); `manuscriptSentence_unitsEquivGLFourEqELFour` (GL_4(R) ≅ R^× by the prefix code; EL_4 = ⊤ via `BinaryLeavitt.elementaryGroup_eq_top`, proved from `glTwo_eq_elementary_holds`) |
| cbb223c4d600 | structural | We identify H with EL_4(R). | OK: `unitsEquivHeadline` |
| a71f65809e0b | formalized | relations; R satisfies the hypothesis of thm:full-defect-ring; MF homomorphisms trivial; R f.g. ⇒ (T) [EJZ] ⇒ f.g. [BHV] | ROUTE GAP (see below). EJZ is `IntegralColumnPlaneClosure.finitelyGeneratedRingGeneralRankElementaryPropertyT` and BHV is `KazhdanFiniteGeneration.fg_of_hasKazhdanPropertyT`; both are OK |
| e47b80780566 | formalized | Since e_{12}(1) ≠ 1, H is nontrivial. | OK |
| 2a57c4750c2a | structural | Let N be a normal subgroup of H. | OK |
| 2bf4b5aca1b4 | formalized | purely infinite simple [AbramsAranda], therefore exchange [AraExchange], so the sandwich [Preusser, Thm 3] | OK: the AGP idempotent form, `isExchangeRing_of_isPurelyInfiniteSimpleRing`, `preusser_sandwich_of_isExchangeRing` and `manuscriptSentence_rankFourSandwich` (Preusser Propositions 20 and 21 proved) |
| e4440282ed35 | definition | EL_4(R,I) and C_4(R,I) | OK: `relativeElementary`, `congruenceSubgroup` |
| 7a20735318a1 | formalized | R simple: I = R or I = 0 | OK |
| 9085fad2968e | formalized | commuting with e_ij(1) forces a scalar; with e_ij(a), a central scalar | OK |
| d38df1795c78 | formalized | λ ∈ Z(R) = F_2 [ArandaCrow], N = 1 | OK: `BinaryLeavitt.center_eq_bot`, `central_units_trivial` |
| bfd4d3ceba5a | formalized | So H is simple. | OK: the printed route is assembled by `PreusserAssembly.isSimpleGroup_elementaryGroup_binaryLeavitt_via_preusser` |
| 8ed259b70c4a | formalized | nontrivial, every MF hom trivial, so H is not MF | ROUTE NOTE (see below) |
| ecb74cabf11a | formalized | since R ≠ 0 satisfies the hypothesis, cor:one-sided-ring-maximal gives the C*_r and C*_max clauses | ROUTE GAP (see below) |
| a621da4b1382 | structural | All rings unital and associative. | OK |
| c0fe92a1903d | definition | equivalent and infinite idempotents; purely infinite [AGP, Def 1.2] | OK |
| 4fb6ccd3e134 | formalized | L_k(1,d) purely infinite simple [AbramsAranda] | OK: `AryLeavitt.isPurelyInfiniteSimpleRing`, for every field k and every d ≥ 2 |
| 8fdc908a49c7 | definition | GL(R), EL(R), EL(R) normal by Whitehead's lemma, K_1(R) | OK: the instance proof carries Whitehead |
| 1f5ca4f92217 | definition | κ : R^× → K_1(R) | OK |

## Gaps found

1. a71f65809e0b: the MF-homomorphism clause is proved from `rankFour_actualCoronaMFResidual_eq_top`, a rank-four
   configuration argument. It is not proved by applying thm:full-defect-ring to R, and no declaration states that R
   satisfies the printed hypothesis: ts = 1 and 1 − st full, with s = s_0 and t = t_0, witnessed by t_1(1 − s_0t_0)s_1 = 1.
2. 8ed259b70c4a: "so H is not MF" comes from `not_isCDEOperatorMF_of_actualCoronaMFResidual_eq_top`. The printed inference
   is nontrivial plus every MF homomorphism trivial, applied to the identity map.
3. ecb74cabf11a: the carriers are `ReducedCStarConsequenceRankFour`, a generic countable-group fact plus ¬MF, and
   `MaximalCStarNotFiniteRankFour`, which uses prop:max-infinite directly. The latter is in projection form plus
   ¬Dedekind-finite, so the printed proper isometry `star v * v = 1 ∧ ¬ IsUnit v` never appears. Neither applies
   cor:one-sided-ring-maximal to R.

## CLAIM

CLAIM binary-example printed-route carriers GroupApproximation/Manuscript/NonMFSentences/BinaryExamplePrintedRoute.lean

The module will state and prove:
- the printed hypothesis of thm:full-defect-ring at R;
- the MF-homomorphism clause, by the closed thm:full-defect-ring endpoint at (R, s_0, t_0, n = 4);
- "not MF" by the printed inference;
- the C* clauses, by the closed cor:one-sided-ring-maximal endpoint at n = 4, with the literal proper isometry.

## Progress log

- 2026-09-13: ledger landed; printed-route module claimed.
