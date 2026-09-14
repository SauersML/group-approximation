# audit-nm-4: fidelity audit, non-MF tex 1338–2507 (the ct block 1541–1807 included)

Lane of session nonsofic-existence-49 (wave 3). Brief: main's scratchpad `ct/ROSTER-wave3.md`. The 23:12 resume
widened the range to 1338–2507, absorbing ct-sentences' block, because ct-sentences was not resumed.

## CLAIM

CLAIM audit of every census row graded formalized/definition for non_mf_groups_exist.tex 1338–2507. Report only;
no Lean landed by this lane.

## Scope and evidence

- Census: merge at 0e622f840 (21:37, base 16d890864). Manuscript SHA-256 in its header equals origin's tex
  (0c4ada3c…, tex unchanged since 73a84cd9c). Rows in range: 232 = 198 formalized + 34 definition
  (chain recurrence 118+20, amenable traces and Clifford lamps 64+13, torsion-free example 16+1). Origin and
  bibliography (2223–2507) have no formalized or definition rows.
- Root reachability: an import-closure index over origin fb68489eb (root wired through 7d71bbbd1) finds all 591
  carrier declarations, in 158 modules, and every one is reachable from `GroupApproximation.lean`.
- Axiom closures: 99 carriers have module-level `#audit_closed_axioms` lines. For all 591, one audit-only probe
  module (never landed, deleted afterwards) ran `#audit_axioms` on each name. Probe 0914-003721-12747, base
  41de120e8: BUILT, `Build completed successfully`, PROBE GREEN. The macro throws on any axiom outside
  propext / Classical.choice / Quot.sound, so every carrier's transitive closure is classical. The probe hop
  died before the local green record was written; the summary was read from the remote output file.
- Method: each printed sentence read from origin against the displayed statement of its carriers (quantifiers,
  hypotheses, constants), with proof bodies read where a route is printed. Subsumption: a stronger carrier must
  imply the sentence. Definitions checked against the printed text: `IsOperatorMF` and `mfHomKernel` (tex 86–122),
  `printedDefect` (eq:intrinsic-defect), `IsMetricChainRecurrent`, `IsPrintedLEFRing` (iff proved with
  `Pestov91.IsLEFRing`), `defectS/defectT/defectD`, `IsLocallyMatricial`, `relativeElementary`,
  `coreTransientIdeal`, `IsAmenableTrace`, `IsQuasidiagonalTrace`, `IsLocallyResiduallyFinite`, `CliffordLamp`
  (a `PresentedGroup`), `gammaBar` (`PrintedGammaBarAffine`), `Suitable`, `IsAcylindricallyHyperbolic`,
  `IsStableRankOne` (dense invertibles), `IsSimpleCStar`, `HasUniqueTracialState`, `IsCDEOperatorMF`,
  `IsMFAlgebra`, `PrintedFournierFacioData`.

## Verdicts: 231 PASS, 1 GENERALITY-GAP, 0 FALSE-GREEN, 0 ROUTE-DIFF

### GENERALITY-GAP

- **f5264e48f943** (l.1489, lem:transient-matrices, owner ms-inverses-3). Printed: "A compact subset $C\subset U$ has a
  finite cover by wandering clopen sets, say $m$ of them, so each orbit meets $C$ in at most $m$ points." Carrier
  `ClopenCrossedProduct.exists_wandering_clopen_cover` (Dynamics/TransientSupport.lean:209) assumes
  `{K : Set X} (hK : IsClopen K) (hKY : Disjoint K Y)`, so it covers clopen K only. `exponentBound_of_wanderingCover`
  handles any covered C, and nothing among the row's declarations shrinks a compact C ⊆ U into a clopen K ⊆ U. The
  fix is one standard lemma (in compact zero-dimensional X, a compact C inside the open U = X∖Y lies in a clopen
  K ⊆ U) named in the row. The proof's later use takes C clopen, so no downstream row is affected.
  Proposed override: `f5264e48f943 partial <same decls> audit-nm-4 GENERALITY-GAP: carrier needs IsClopen K; printed
  compact C; add compact-to-clopen shrink`.

### Notes on PASS rows

- **N1** (1baaaaa0fb29, 69ef136d809a; prop:bilateral-three). `PrintedBilateralThree` kills `relativeElementary (Fin n)
  (defectIdeal T k)`, where `defectIdeal` is the span of compressed-clopen defects. The printed I follows through the
  proved `defectIdeal_eq_transientIdeal_chainRecurrentSet` (Manuscript/ChainCore/TransientIdealDefectSpanConsumers).
  Suggest naming it in both rows.
- **N2** (2416b0e3e06b). The two block-root sentences are carried inside `elementaryGroup_matrix_zmodTwo_eq_top` through
  `elementaryBlockGroup_map`, which the row does not name; the route matches the print.
- **N3** (8cde0b44b52f). The declarations prove only that ℤ is amenable. "W/W_0 ≅ ℤ" comes from `manuscriptSentence_reassociation`
  (row 9355c08e7f2b), and the directed union is immediate. Suggest adding that declaration.
- **N4** (c650b0a20b89). The map note quotes the next sentence (Hull Cor 5.7 / Lemma 5.8), and the declarations include
  that sentence's carriers. The printed sentence follows from `osinLemma71Printed` and `manuscriptSentence_saturationSuitable`.
  The mismatch is cosmetic.
- **N5** (a60285a8682e). The lamp part is `manuscriptSentence_finiteInvariantSubgroup`, and the Γ_n-coordinate part is row
  edc038ff7b5f's `manuscriptSentence_finiteSubsetOneLevel`.
- **N6: systemic caution, torsion-free step rows** (the 16 keys marked N6). Each carrier proves the printed
  inference with its printed premise as a binder:
  - c3246ffe1961 binds `hlift`, clause (e) of Hull's Theorem 7.1 as used in thm:hull;
  - 9d87872de931, 92115dd7edef and f2bf6328169e bind acylindrical hyperbolicity of Q as an instance;
  - 8e8d5f3f8be0 through 871771af6cba bind the Fournier-Facio data `PrintedFournierFacioData` (cited construction, FFF §2).
  Those premises are graded partial on their own rows: thm:hull 8aead549f1fe/4895f03fdf5f/bcc99703f838, lem:saturation
  2f55113239ce/2d1cd22e5f49/2f997e5af4e6/721da4c14d11, FFF 8097c371f35d/dab2f2bfe084, and the corollary statement rows
  7b1fa3182135/8b1ec28a0e73, all over the Osin waist residuals. So the 16 PASS verdicts are step-level: they do not
  close thm:torsion-free or cor:regular-nonmf-algebra, and a count of formalized rows in this section must not be read
  as closure. DGO 2.35, GO 1.1, Osin 1.2 and Osin 7.1 themselves are closed, universally quantified carriers
  (the probe includes them).
- Routes verified by reading proofs:
  - 1a88ddc187c0: permutation matrices of the regular action of the finite local models (`isNormApproximable_of_isLEF`).
  - 77028123cdd6: residual finiteness of GL_4(ℤ) by reduction mod |z|+1 of an off-identity entry. (T) of Γ̄ is a
    closed quotient of the literal base; a cited result, route free.
  - 2d5721555dfe: GHW Theorem 4 is the closed `printedGHWTheoremFour`.
  - 2c614717a212: Elek–Szabó is the closed `SoficByAmenablePermanence` result.
- Subsumption by stronger carriers:
  - 01d34ed18b0a: the carrier has no countability hypothesis.
  - 1d52a79f1fef: density of periodic points from agreement on [0,m] plus shift invariance.
  - PrintedFixedCore* rows: totally disconnected compact metric spaces, nonemptiness not required.

## Row ledger

- **sec:chain-core** (11): 275bedb28f9f l.1345 d PASS; 752564275a33 l.1345 d PASS; a1bda19b475a l.1351 f PASS; 8a557cb954fb l.1351 f PASS; 6011dc411b20 l.1351 d PASS; 2d1ca8689ac6 l.1351 d PASS; b1a4887c5412 l.1351 f PASS; 1d0bcc92a75f l.1351 f PASS; 1a88ddc187c0 l.1351 f PASS; 49f76a64907a l.1364 d PASS; d5af28721656 l.1364 d PASS
- **lem:chain-core-models** (41): 0ae6fc9e199c l.1372 f PASS; 73bd8ac910aa l.1372 f PASS; 9bc3873fb872 l.1380 d PASS; 078684fc2a60 l.1380 d PASS; dfc6d4510272 l.1386 f PASS; 8bf7f40918d5 l.1386 f PASS; 56b6a80cc911 l.1386 f PASS; 2ed7f807a3a6 l.1386 f PASS; 57cd1b63930c l.1386 f PASS; 0941296cf395 l.1386 f PASS; 4aede6d48b4d l.1386 f PASS; b94a006ee638 l.1386 f PASS; 9ea50b0ff631 l.1402 d PASS; cbf45b0e1c51 l.1402 f PASS; 1d52a79f1fef l.1402 f PASS; b39310f67614 l.1402 d PASS; 758517bf8d56 l.1402 f PASS; 647f44a95b8a l.1402 f PASS; ffa61d258258 l.1402 f PASS; 048953d87f92 l.1415 f PASS; ae9c3d8b9922 l.1415 f PASS; 4fc54b29a740 l.1415 f PASS; a08f25fce44c l.1415 f PASS; d8f8d764406c l.1422 f PASS; 9c49a2efb0ca l.1422 f PASS; 854ec7cb0423 l.1422 f PASS; 3ef2a7cdb9bd l.1422 f PASS; 3d8a2204752a l.1428 f PASS; fe2bd83087c0 l.1428 f PASS; 4bb19e581840 l.1428 f PASS; ed348643e2ad l.1428 f PASS; 807793f12a5e l.1439 f PASS; e6626f95fede l.1447 f PASS; 2583cbd0c0f2 l.1447 f PASS; 3b218f92cd81 l.1447 f PASS; fb195144e5c2 l.1447 f PASS; 8921296d639a l.1447 f PASS; 042966c81c7e l.1456 f PASS; 549aa93e832f l.1456 f PASS; bba38420cf8b l.1462 f PASS; eda117e756e6 l.1465 d PASS
- **lem:transient-matrices** (11): 7ff20576d4cf l.1470 f PASS; 910136e6e66d l.1482 f PASS; c05b0ec8b821 l.1482 f PASS; 97e43ae93d14 l.1482 f PASS; 2546c17d9884 l.1482 f PASS; f5264e48f943 l.1489 f GENERALITY-GAP; 1687471008a1 l.1489 f PASS; 741b64286b55 l.1489 f PASS; d01cbef361ce l.1502 f PASS; 2a63696d979b l.1502 f PASS; e55132ef58f5 l.1502 f PASS
- **thm:core-ring-reflection** (2): 5a62e295ac1a l.1527 d PASS; d74779471003 l.1527 f PASS
- **prop:bilateral-three** (6): 1baaaaa0fb29 l.1543 f PASS N1; 69ef136d809a l.1543 f PASS N1; b98536a82318 l.1550 d PASS; 8985ec7b13b2 l.1594 f PASS; 7f55f9a11e5a l.1594 f PASS; 512b53c80bd2 l.1594 f PASS
- **thm:core-mf-radical** (19): ccfc792cc48b l.1610 d PASS; 521214409259 l.1614 f PASS; e94a545b030a l.1614 f PASS; 84bacecbfa4c l.1621 f PASS; cc05d5f6226c l.1621 f PASS; 3b9dae111508 l.1626 f PASS; be106727feb1 l.1626 f PASS; 4c62dd1963db l.1626 f PASS; fd54e2645afe l.1634 f PASS; 2416b0e3e06b l.1634 f PASS N2; 8ffeafc81808 l.1634 f PASS; c13ca7c28028 l.1634 f PASS; a47d16c7fbe5 l.1634 f PASS; a1d5cde2c840 l.1643 f PASS; 7e27335fac44 l.1643 f PASS; 0b84b12a0927 l.1651 f PASS; aef6776a7348 l.1651 f PASS; 646debe8463c l.1651 f PASS; a3bd73fe42e9 l.1658 d PASS
- **lem:involution-localization** (10): 9eb0c9e85459 l.1664 d PASS; d04eb3acd5c8 l.1664 f PASS; b13eccd8f0ec l.1664 f PASS; c869a1161522 l.1673 f PASS; 7bfb9f44e634 l.1673 f PASS; a434801aeca5 l.1673 f PASS; ad9e7459d990 l.1673 f PASS; 05241abb9a90 l.1673 f PASS; 4e4b1729199c l.1673 f PASS; f7ca9d694948 l.1673 f PASS
- **cor:dynamic-rank-budget** (38): 34c348ec46b9 l.1697 f PASS; 36ddcaf60cbb l.1697 f PASS; 3ea1fdec31e9 l.1697 f PASS; 3e7b0d067ef3 l.1697 f PASS; d44d8916b7e9 l.1708 f PASS; 18794db09df6 l.1708 d PASS; 0c51973a1e22 l.1716 f PASS; 6594ce123649 l.1716 f PASS; c3d333b41241 l.1716 f PASS; 32b097ac7fe8 l.1721 f PASS; 5d45868395fb l.1721 d PASS; 709190a010a1 l.1721 f PASS; 5a2063e21671 l.1721 f PASS; 48a7b49cd9cc l.1721 d PASS; 215bfbb4bef3 l.1731 f PASS; d29d95ef4834 l.1731 f PASS; 197439992d5d l.1752 f PASS; 4c1aa0bcba19 l.1752 f PASS; ded50f77e36b l.1752 f PASS; 01623e90c350 l.1760 f PASS; 7596b825ecdb l.1760 f PASS; 49b5df732076 l.1760 f PASS; ce4eb6ceb71b l.1769 f PASS; 54044aad03be l.1769 f PASS; 9fdbaf282687 l.1769 f PASS; fbee156f2d6d l.1769 f PASS; 5c75b0bf2db4 l.1778 d PASS; 9c225384feb2 l.1778 f PASS; a7eb8076fde4 l.1778 f PASS; 9ac1eedef5a7 l.1778 f PASS; 02525ddc3aa4 l.1778 f PASS; c8c11f6bb25a l.1778 f PASS; dba179ef6f13 l.1778 f PASS; fb84c069f1fe l.1778 f PASS; f31fa0413ffd l.1794 f PASS; 2d5721555dfe l.1794 f PASS; dd5ef3eafd48 l.1794 f PASS; 5e4354e1556b l.1794 f PASS
- **sec:amenable-nonqd** (5): 4daee6130a7d l.1812 d PASS; 3f53897704ba l.1812 d PASS; f02bfca27b23 l.1824 d PASS; ca353970e9e3 l.1827 d PASS; c9da12b3f699 l.1827 d PASS
- **thm:factorization-nonmf-trace** (6): 01d34ed18b0a l.1836 f PASS; fa19477760b9 l.1845 f PASS; 0fbd72617dcb l.1845 f PASS; 1c2804634e53 l.1845 f PASS; 53f02dc594db l.1845 f PASS; a817c6ae86c9 l.1856 d PASS
- **prop:locally-rf-by-z-trace** (26): fd8372f71c2d l.1861 f PASS; 0bd25ebcbeac l.1861 f PASS; a97f0ab46cd9 l.1869 f PASS; 94ebd1377c15 l.1869 f PASS; 6e563dbca22b l.1880 f PASS; 30eb3e57ac10 l.1880 f PASS; da2fd300384a l.1880 f PASS; 89bc31ec5034 l.1893 f PASS; 1ea7f92c66a1 l.1901 f PASS; b77ceccea9ed l.1901 f PASS; 23d58dbda4bf l.1913 f PASS; 8e53d32e3fb8 l.1920 f PASS; 60898a519f4f l.1920 d PASS; c180c0186454 l.1920 d PASS; d5c52ca23af0 l.1933 f PASS; 08844a3bdb91 l.1933 d PASS; 86ba78fb0d96 l.1933 f PASS; dc43ec6b23ed l.1943 f PASS; 4704b74b6c8e l.1949 f PASS; 1fab0dcc8e88 l.1949 f PASS; b9ca7188b1f5 l.1949 f PASS; 407925e64c6c l.1960 f PASS; 51284d178433 l.1960 f PASS; c41bad22d29b l.1960 f PASS; ad753104ce33 l.1960 f PASS; 5306701b688c l.1960 f PASS
- **prop:clifford-self-embedding** (10): 8abb5071b65b l.1979 f PASS; 7732f82e8623 l.1979 f PASS; 177456a78260 l.1986 f PASS; a0acefd07ec1 l.1986 f PASS; dba28fb94e6d l.1986 f PASS; 91502a70ae59 l.1986 f PASS; b33af3eb4b3c l.1986 f PASS; 24b5330b38b0 l.1986 f PASS; 013d2e0e8b4a l.1986 f PASS; 28740c0c5a93 l.1986 f PASS
- **prop:clifford-locally-rf** (30): a2ba60db6a3b l.2006 f PASS; 93aa71e6b818 l.2012 f PASS; a0abcf4e0a16 l.2012 f PASS; 9355c08e7f2b l.2019 f PASS; bc2d73bb124a l.2024 d PASS; 4cdae54eba21 l.2024 f PASS; 404ff3b063bf l.2024 f PASS; edc038ff7b5f l.2033 f PASS; e4ebdec3bbab l.2033 d PASS; a60285a8682e l.2033 f PASS N5; 2a24a52c111f l.2040 f PASS; 675969466d3b l.2040 f PASS; 9f522f4b56dd l.2040 f PASS; ab3b4185d7d4 l.2040 f PASS; bba6a4ecce85 l.2040 f PASS; 508294d77cb5 l.2040 f PASS; 8cde0b44b52f l.2051 f PASS N3; 2c614717a212 l.2051 f PASS; f1f1ba4ba319 l.2051 f PASS; a998ccfa2015 l.2051 f PASS; 86d7bbda9474 l.2062 f PASS; 42ae3f886537 l.2062 f PASS; 3229365c29c6 l.2074 d PASS; 77028123cdd6 l.2083 f PASS; e947a3d4f4a1 l.2083 d PASS; 80c65e0771e4 l.2093 f PASS; c48c7da870a2 l.2093 f PASS; 8c17c33ec225 l.2093 f PASS; 7f667d9f1cb7 l.2093 f PASS; 4ce81a3db24b l.2100 f PASS
- **sec:torsion-free** (1): 615720614d7a l.2114 d PASS
- **lem:saturation** (13): c650b0a20b89 l.2144 f PASS N4,N6; 24d44fae17ad l.2144 f PASS N6; c3246ffe1961 l.2144 f PASS N6; 02b6bf87400f l.2160 f PASS N6; 26237422bf4c l.2160 f PASS N6; 8e8d5f3f8be0 l.2172 f PASS N6; d8d9d495865d l.2172 f PASS N6; 56f937d2ec19 l.2182 f PASS N6; 9d87872de931 l.2182 f PASS N6; da4a1c0beff4 l.2190 f PASS N6; d29816e1de56 l.2190 f PASS N6; eef4d274766e l.2196 f PASS N6; 871771af6cba l.2196 f PASS N6
- **cor:regular-nonmf-algebra** (3): 92115dd7edef l.2210 f PASS N6; f2bf6328169e l.2210 f PASS N6; b7b49212cd37 l.2210 f PASS N6

Legend: f = formalized, d = definition. Verdict PASS unless stated; N1–N6 refer to the notes above.
