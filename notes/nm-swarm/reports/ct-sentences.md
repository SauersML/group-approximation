# Lane ct-sentences: census and truth audit of tex 1541–1807 and Introduction 249–259

Written by ct-sentences only (lead: the ct-* coordinator session).  Tex at origin 3d9b2c4f0; the last tex
commit is 73a84cd9c (15:23).  Keys come from the census lane's regenerated join `merge-0913-160921`
(manuscript SHA-256 `0c4ada3c…`, after 73a84cd9c).  They are `key_of` of the extracted sentences and
were not recomputed here.

## Totals

121 sentences: 5 in the Introduction paragraph (census line 249) and 116 in tex 1543–1794.  All are
`unassigned` on main.  In the census worklist, 10 keys are chain-radical's and 111 are
"unowned (new since 45483f699)".

| owner | rows |
|---|---|
| ct-bilateral-cell | 14 |
| ct-bilateral-mf | 12 |
| chain-radical (thm:core-mf-radical; 10 rows rekeyed by 73a84cd9c) | 22 |
| chain-core | 1 |
| chain-reflection, jointly with ct-bilateral-mf | 1 |
| ct-involution | 17 |
| ct-return-tower | 15 |
| ct-rank-budget | 17 |
| ct-two-ended | 12 |
| ct-rank-two-limit | 4 |
| structural (rows landed by ct-sentences) | 6 |

## Findings

1. **Census splitter (census lane; not edited here).** `protect` replaces `ABBREV + "."` with no word
   boundary, so a sentence ending in "…ed." or "…al." does not split.  Rows `ded50f77e36b` ("…is killed.
   Core restriction has LEF image…") and `5e4354e1556b` ("…are trivial. The same reasoning applies to
   unit groups…") each hold TWO printed sentences, and their carriers must cover both.
2. **Content carried only by displays.** The census drops unnumbered displays, so each fragment below is
   the only row for its display.  None of them may be graded `structural`:
   `ccfc792cc48b` (K_n), `e94a545b030a` "Moreover," (Rad_MF(GL_n)=K_n for n≥3, Rad_MF(EL_n)=K_n for n≥4),
   `4c62dd1963db` "For n≥2," (GL_n(B)=EL_n(B)≅∏SL_{nh_a}(F_2)), `732be542bd63` (r and W),
   `4a0223a24da4` "Put" (c, ℓ, y, z, B), `4f649a2dcbfa` (WcW⁻¹, δ, [y,δ]=z⁻¹), `10fe7a237145`
   "The identities" (the two kill identities), `18794db09df6` (C_i), `48a7b49cd9cc` (D_i, a_i, b_i),
   `d29d95ef4834` (Φ), and `fbee156f2d6d` (R_X^×≅GL_fin(ℤ,F_2)⋊ℤ).
3. **Truth audit by hand: no printed claim is false.**
   - Cell, under [g,h]=ghg⁻¹h⁻¹ (tex 156).
     - Levels: T^{-j}(D)∩P=∅ for j≥1, since x∈P∩T^{-1}D gives T(x)∈D∩T(P)=∅.
     - W=diag(u,u,ur), and ur fixes −1 and −2, so WcW⁻¹=e13(f_{0,−2}).
     - [e13(x),e21(q)]=e23(−qx) with q·f_{0,−2}=f_{0,−2}, so δ=e23(−f_{0,−2}).
     - In the (2,3) block, [e32(a),e23(b)]=diag(1,1+ab) when ba=0; with a=f_{−1,0} and b=−f_{0,−2},
       this gives [y,δ]=1−E33 f_{−1,−2}=z⁻¹.
     - [z,e31(f_{−2,0})]=e31(f_{−1,0}), and [e23(f_{0,−1}),e31(f_{−1,0})]=e21(f_{00})=e21(d).
     - These are 2-step nilpotent calculations, so the opposite convention gives the same identities.
       Only characteristic ≠ 2 can detect a sign error.
   - Tower.
     - If x∈D_i and x+i=y+j with y∈D_j and i≠j, then one of x, y is a return of the other strictly
       before its return time.  So b_i a_j=0.
     - Every point has a unique last past visit to C within 2r−2 steps, because
       T^{−r}(c)=T^{j′}(c′) with |j′|<r.  So Σ_i a_i b_i=1.
   - Two-ended example: the tails from −N and N have codimension 2N−1, and their image under the tail
     translations z^{a₋}, z^{a₊} starts at −N+a₋ and N+a₊, so its codimension is 2N−1+a₊−a₋.
4. **Model tests** (`GroupApproximation/Dynamics/ChainCoreTailModels.lean`, closed `decide +kernel`
   checks).
   - The cell in the cyclic 5-level model at p=2 and p=3, with centralizers and W on level-zero roots.
   - Sign controls that fail at p=3 and are blind at p=2 (the calibration case).
   - The r=2 and r=3 tower models, with a negative control.
   - These are NOT carriers; no census row names them.

## Ledger (key → owner; status on main is `unassigned` unless marked)

### Introduction (census line 249, label thm:headline)
- `7cb6740cda5d` chain-radical — "The obstruction also computes entire MF radicals in a different family."
- `307b3272f639` chain-core (definition of R_X, ClopenCrossedProduct) — "For a homeomorphism T … let R_X be …"
- `c890294ad9b0` chain-reflection (universal directly finite quotient) + ct-bilateral-mf (R_X directly finite ⟺ GL_3(R_X) MF)
- `518c40eb5865` chain-radical (GL_n n≥3 consumes ct-bilateral-mf; EL_n n≥4)
- `58fcf9019fc9` ct-rank-budget — "If T is aperiodic, the same conclusion holds already for the unit group …"

### prop:bilateral-three (tex 1541–1607)
- ct-bilateral-mf: `1baaaaa0fb29` (GL_n MF ⟺ LEF ⟺ directly finite), `69ef136d809a` (kills EL_n(R_X,I))
- ct-bilateral-cell: `331807e9e898` (clopen P, D), `b98536a82318` (p, d, f_ab), `30e2f83b735e` (wandering matrix units),
  `8a69e48d6382` (negative levels outside P), `7753d17ede98` (S, ts=p, st=p−d)
- ct-bilateral-mf: `ca8edac58ba3` (S f.g., EL_3(S) (T) via `ejz`)
- ct-bilateral-cell: `9a398d134788` (corner embedding), `732be542bd63` (r, W display), `f60fa6d3b787` (r centralizes L),
  `4a343ef108b1` (W L W⁻¹ ⊆ L, a ↦ sat), `0fa967251251` (W fixes −1, −2), `4a0223a24da4` (c, ℓ, y, z, B display),
  `4f649a2dcbfa` (c∈C_B(L) and the three identities), `15fba9954989` (z commutes with L, W, c, y),
  `10fe7a237145` (the two kill identities display)
- ct-bilateral-mf: `cd7908a482b5` (z∈𝔇_B(L)), `e94a87793eb1` (⟨z⟩ finite central, order char k), `3550126258fb`
  (compression criterion kills z), `8985ec7b13b2` (kill the defect root), `7f55f9a11e5a` (roots of the ideal of d),
  `512b53c80bd2` (rank n≥3), `0f83142a750a` (defects generate I, lem:transient-matrices), `2016c672dd6a`
  (not directly finite ⇒ not MF), `d812630a48ab` (directly finite ⇒ LEF, thm:core-ring-reflection)
- structural, landed: `bb034089918b`, `37c90a2ab256`

### thm:core-mf-radical (tex 1609–1656): chain-radical
- still keyed in chain-radical's plan: `3b9dae111508` `be106727feb1` `4c62dd1963db` `fd54e2645afe` `2416b0e3e06b`
  `8ffeafc81808` `c13ca7c28028` `a47d16c7fbe5` `0b84b12a0927` `aef6776a7348`
- rekeyed by 73a84cd9c (unowned by key in the worklist): `ccfc792cc48b` (K_n display), `521214409259` (K_n=EL_n(R_X,I)
  locally finite), `e94a545b030a` ("Moreover," = the radical display), `84bacecbfa4c` (EL restriction surjective, LEF quotient),
  `cc05d5f6226c` (GL quotient = LEF restriction image), `0c22aa9f1005`, `2b6b9904f2d6` (GL kill via prop:bilateral-three:
  consumes ct-bilateral-mf), `a1d5cde2c840` (EL n≥4 via prop:torsion-defect-ring), `7e27335fac44` (countability),
  `646debe8463c` (GL image inside GL_n(R_Y))

### Remarks after thm:core-mf-radical (tex 1658–1661)
- structural, landed: `2ae0af7a44d9`, `42fd272878ba`
- ct-involution: `a3bd73fe42e9` (notation K_n(I), also n=1 and corners)

### lem:involution-localization (tex 1663–1694): ct-involution
`9eb0c9e85459` `d04eb3acd5c8` `b13eccd8f0ec` `c869a1161522` `7bfb9f44e634` `a434801aeca5` `ad9e7459d990` `07ab0fbe6cfc`
`3468c60b2946` `05241abb9a90` `4e4b1729199c` `6baf73489057` `f7ca9d694948` `50c5dd41dff4` `5c06eec5555b` `1c114e2c4209`

### cor:dynamic-rank-budget (tex 1696–1767)
- ct-rank-budget, statement: `34c348ec46b9` `36ddcaf60cbb` `3ea1fdec31e9` `3e7b0d067ef3`; proof: `6b63a354455d` (r=2, r=3)
- ct-return-tower: `d44d8916b7e9` (cover U_i), `18794db09df6` (C_i display), `0c51973a1e22` (C clopen, separated, covers),
  `6594ce123649` (gaps in [r,2r−1]), `c3d333b41241` (r=1), `32b097ac7fe8` (C_h, S_C), `5d45868395fb` (p_C, P_C),
  `709190a010a1` (v implements S_C; P_C ≅ LC(C,k)⋊ℤ), `5a2063e21671` (finite splitting), `48a7b49cd9cc` (D_i, a_i, b_i display),
  `215bfbb4bef3` (tower identities), `60708f733247` (unital corner of M_{2r−1}(P_C)), `d29d95ef4834` (D_i=C for i<r; Φ),
  `9e22ceae062f` (unitization), `f1769ba5e51c` (block elementary flattening)
- ct-rank-budget, proof: `1cddd9e4b7ba` `7da9f1c6076f` `8f8f0c7b59fa` `d5dcf496d149` `e7f732e9cb78` `197439992d5d` `4c1aa0bcba19`
  `ded50f77e36b` (two sentences, finding 1) `01623e90c350` `7596b825ecdb` `49b5df732076`

### Two-ended example (tex 1769–1792): ct-two-ended
`ce4eb6ceb71b` (period hypothesis cannot be removed) `54044aad03be` `9fdbaf282687` `fbee156f2d6d` (unit group display)
`5c75b0bf2db4` `9c225384feb2` `a7eb8076fde4` `9ac1eedef5a7` `02525ddc3aa4` `c8c11f6bb25a` `dba179ef6f13` `fb84c069f1fe`

### Rank-two limitation (tex 1794–1807)
- structural, landed: `5c87b6c2f4ed`, `076047e005df`
- ct-rank-two-limit: `f31fa0413ffd` `2d5721555dfe` `dd5ef3eafd48` `5e4354e1556b` (two sentences, finding 1)

## Progress log
- 09-13 ~16:35: ledger, six structural rows and hand audit (no refutation) LANDED 03e7714ae.
- 09-13 ~16:40: `GroupApproximation/Dynamics/ChainCoreTailModels.lean` LANDED 313212d8a (probe 0913-163538-71262 GREEN,
  BUILT line checked). All printed cell identities hold at p = 2 and p = 3; the sign controls fail at p = 3 and are blind at
  p = 2; the r = 2 and r = 3 tower identities hold, and the wrong cut fails. Not wired, and no row names it.
- Carrier sweep at ~16:40: two ct Lean landings, both scaffolds with no closed endpoint, so no row is graded yet.
  - ct-bilateral-mf dfc4d5221 `Manuscript/ChainCore/BilateralThreeGroupKill`: the group-level half of the proof of
    prop:bilateral-three over the printed relations as hypotheses (`bilateralB`, `commute_of_mem_bilateralB`,
    `killed_of_finite_central_defect`, `root_killed_of_finite_central_defect`). Planned statement module
    BilateralThreeStatement: `PrintedBilateralThree` over BilateralThreeCellStatement (ct-bilateral-cell),
    ClopenCrossedProductCountableStatement (chain-core), ClopenCrossedProductDirectlyFiniteLEFStatement (chain-reflection)
    and ClopenCrossedProductNonzeroDefectStatement (chain-matricial + chain-reflection).
  - ct-rank-budget fbd3fae3c `Manuscript/OneSidedMFRadical/MFRadicalTransport`: MF-radical transport along embeddings
    and conjugation, and direct finiteness through tower corners (general lemmas, `#audit_axioms`).
  - The owning lanes append their own rows (COMMON_RULES rule 14); this ledger records the carriers once endpoints close.
- 09-13 ~17:00, lead's item "take one builder leaf": at the survey all four candidates had started, and the largest
  unstarted piece was tex 1774–1792 of the two-ended example (9 keys: fbee156f2d6d 5c75b0bf2db4 9c225384feb2 a7eb8076fde4
  9ac1eedef5a7 02525ddc3aa4 c8c11f6bb25a dba179ef6f13 fb84c069f1fe).
  - ~16:57: one message to ct-two-ended proposing a split. (A) ct-sentences: GL_fin(ℤ,F₂) ⋊ ℤ is LEF, and the tail symbols
    agree by the codimension count. (B) ct-two-ended: R_X^× ≅ GL_fin ⋊ ℤ and the closing sentence.
  - OVERLAP found after sending: ct-two-ended's `Algebra/FinitaryGeneralLinear.lean` (attic a51d90dda, 17:01) already
    builds `FinitaryGL.GLfin k`, `shiftGL k`, `shiftAction k` and `FinitaryShift k`. Whatever the reply, ct-sentences
    does NOT restate those objects. If (A) is agreed, it consumes these names once that module lands green:
    `PrintedFinitaryShiftLEF : Prop := Sofic.IsLEF (FinitaryGL.FinitaryShift (ZMod 2))`, and the tail-symbol Prop over
    `FinitaryGL.GLfin (ZMod 2)` and `FinitaryGL.shiftGL`.
  - Waiting on ct-two-ended's reply; nothing authored for this piece.
