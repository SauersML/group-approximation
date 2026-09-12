# lx-pzero — the reduced-powers interface for Step D mod p (LIX strongest swarm)

Owns `CharClass/OddPUnit*`, `OddPZero*`, `OddPNormal*`, `OddPTotal*`.  Clone lix-g.

## Design (agreed with lx-design, lx-cartan-b, lx-toppower, lx-torusP, lx-splitK, lx-bundleP)
- PRODUCER `OddPTotal.TotalReducedPowers p`:
  - classes `D X q j : H^q → H^{pq−j}`, natural;
  - `ptotOf D X q x = Σ_{j even ≤ pq} of (pq−j) (D j x)`, multiplicative on even classes (`ptot_mul`, lx-cartan-b);
  - `unit_zero`, `top_two` (lx-toppower);
  - `bad_two` (V in degree 2, lx-cartan-b);
  - unit `μ` with `zero_cp : [D_{2(p−1)} h] = μ h` on H²(CP^M) (lx-toppower / lx-design, T² link).
- CONSUMER `OddPTotal.EvenReducedPowers p`:
  - graded `P X i` (normalised by `μ^{-(d/2−i)}`), with `natural`, `shift`, `unstable`;
  - `Ptot` ring endomorphism, with `ptot_natural`;
  - subring `Good` with `good_natural`, `good_two`, `good_of_components`;
  - `cartan` on `Good`;
  - `mul_single`;
  - `zero_one`, `zero_cp`, `degree_two` (κ = 1).
- No general P⁰ = id and no general graded Cartan: both need universal examples / V', and no consumer needs either.

## GREEN
- `CharClass/OddPTotalInterface.lean` v3 (a5f0a1992): probe 0912-104820-66710 PROBE GREEN, BUILT, axioms clean.

## PRODUCER (12:15 CDT, landed unverified)
- `OddPTotalProducer`: `oddDClass_add`, `oddDAdd` (→+, 0 above pq), `oddDAdd_natural`; named inputs
  `UnitZeroOddP`, `PtotMulOddP`, `TopTwoOddP`, `BadTwoOddP`, `ZeroCPOddP μ`; `totalReducedPowersOddP`,
  `evenReducedPowersOddP` (= `.toEven`).
- `OddPTotalBadTwo`: `badTwoOddP p hp` from V (`OddPCartanVanish.oddDClass_eq_zero_of_not_dvd`).
- Owed by peers: `unitZeroOddP`, `topTwoOddP`, `∃ μ, IsUnit μ ∧ ZeroCPOddP p hp μ` (lx-toppower); `ptotMulOddP`
  (lx-cartan-b).  Spellings sent 12:15.
- Probe history: 0912-114527-61309 red (Grading zero cases, deprecated finset_sum_apply); 0912-120528-42984 red
  (▸ in eq_sum_components).  Both fixed and landed; next group probe ~12:35 (Grading … Packaging + Producer + BadTwo).

## LANDED UNVERIFIED (11:35 CDT, after main was restored)
- de17c2bb1: `OddPTotalGrading`, `OddPTotalPackagingDefs`, `OddPTotalPackagingGood`, `OddPTotalPackagingExpand`,
  `OddPTotalPackagingCartan`.
- (landing now) `OddPTotalPackagingMulSingle`, `OddPTotalPackaging` (`TotalReducedPowers.toEven (hp : 2 ≤ p) :
  EvenReducedPowers p`, every consumer field proved from the producer fields).
- One group probe of all seven modules launched on lix-g.

## (superseded) AUTHORED, UNVERIFIED (on disk + lixs/backup/lx-pzero/, NOT on main)
- `CharClass/OddPTotalGrading.lean` (component/smul/pullback/expansion/projDeg lemmas, GoodDeg arithmetic).
- `CharClass/OddPTotalPackagingDefs.lean` (μinv, component_ptotOf, pieceP/totalP, piecePtot/totalPtot, evenness,
  naturality of ptotOf).
- BLOCKED: becc912bd (session_01PWzwKNBr2dwjX4pucBuXff, 11:10 CDT) deleted 27,760 paths from main; every landing is
  refused for missing imports.  Reported to the lead.  The interface must be re-landed from a5f0a1992 once main is restored.

## NEXT (authoring in order)
1. `OddPTotalPackagingGood.lean`: `IsGood`, `isGood_of`, closure (add/neg/zero/one/mul via `ptot_mul` + degree argument),
   subring `good`, `good_natural`, `good_two`, `good_of_components`, `totalPtot_mul`, `Ptot` ring hom.
2. `OddPTotalPackagingCartan.lean`: expansion `ptotOf a c = Σ_{s ≤ a/2} μ^{a/2−s} • totalP s (of a c)` for good c,
   `cartan_piece` via `projDeg E` of `ptot_mul`, bilinear extension; `mul_single`.
3. `OddPTotalPackaging.lean`: `TotalReducedPowers.toEven : EvenReducedPowers p` (`hp : 2 ≤ p`).

## PEER STATUS (12:30)
- lx-toppower: `unitZeroOddP`, `topTwoOddP` in `OddPTopPowerTotal` (namespace TopPow); waits on lx-diag's OddPDiagonalAug.
- lx-cartan-b: `ptotMulOddP` authored in `OddPCartanTotal` (attic); waits on OddPCompBReal + OddPDiagonalAug.
- lx-endpoint consumes `evenReducedPowersOddP` (binders frozen) inside ProblemLIXStrongFinal.
- UNOWNED (critical path): `∃ μ, IsUnit μ ∧ ZeroCPOddP p hp μ`, which needs the degree-one constant (lx-toppower),
  the T² corner (lx-cartantorus, landed 0a5f05560), and a GEOMETRIC link: one line bundle on T² with nonzero mod-p
  Euler class (one-zero section, ThomStepCEulerOf), pulled back from CP^M.

## SPLIT (independent sub-tasks a helper could author)
- NEW `CharClass/OddPTotalZeroCP.lean`: `zeroCPOddP_exists (p) [Fact p.Prime] (hp : Odd p) : ∃ μ : ZMod p, IsUnit μ ∧
  OddPTotal.ZeroCPOddP p hp μ`.  Inputs: μ as the scalar of `oddDAdd p hp (CPtop M) 2 (2(p−1))` on the line H²(CP^M)
  (naturality + additivity, independent of M via linear inclusions); IsUnit μ via T² (`OddPCartanTorus`), the
  degree-one constant, and a line bundle L → T² with e(L) a unit multiple of t₁t₂.
- `OddPTotalPackagingCartan.lean`, `cartan_piece : Even a → Even b → IsGood (of a c) → IsGood (of b c') →
  R.totalP X i (of (a+b) (cup c c')) = Σ_{j ∈ range(i+1)} R.totalP X j (of a c) * R.totalP X (i−j) (of b c')`.
  Inputs: Defs + Good files, `ptot_mul`, `projDeg_of`, `smul_mul_left`/`mul_smul_right`, `goodDeg_inj`.
- `OddPTotalMulSingle.lean`, `mul_single_piece` (statement as in EvenReducedPowers.mul_single, homogeneous w).
  Inputs: Defs, `ptot_mul`, `component_ptotOf`, `eq_sum_components`.

## NEEDS
- Main restored (lead).
- lx-redpow: R6/R3/R7 + D at general even j; lx-additive: `redPowLin` (eb6eee004, unverified);
  lx-toppower: `top_two`, `unit_zero`, `zero_cp` + IsUnit μ; lx-cartan-b: `ptot_mul`, `bad_two`.

## TRAPS
- Mathlib pin 81a5d257 renamed `finset_sum_apply` → `finsetSum_apply` (DFinsupp, AddMonoidHom) and `coe_finset_sum` →
  `coe_finsetSum`; the old names are deprecated aliases, which are hard errors under warningAsError.
  `Finset.range_subset` is the membership form; the `range m ⊆ range n ↔ m ≤ n` form is `Finset.range_subset_range`.
- `rw [zero_mul, zero_mul]` fails once the first rw has already rewritten both zeros; use `simp only`.
- `DFinsupp.ext` on `TotalHOf`: `show` the goal in `TotalHOf.component` form before rewriting; the raw `x e`
  coercion is not type-correct at instances transparency.
- 11:10 CDT: becc912bd (another session) deleted 27,760 paths from main; the lead restored forward.  Keep scratchpad
  backups of every authored file until it lands.
- Unused binder in a structure field type (`hd`) is a hard lint error; name it `_hd`.
- `git grep -E` has no `\b`: a pattern with `\b` matches nothing (silent miss).
