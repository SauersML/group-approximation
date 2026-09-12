# Lane `lix-descent` (successor of `sp-descent`) — `λ₁ = ((p−1)/2)!`, generic in `p`

Owner of `GroupApproximation/CharClass/OddPDescent*.lean`.  Clone `spare1` (lix-h was never created).  Started 2026-09-11 ~21:20 CDT.

## STEP 0 (2026-09-11)

* `sp-descent.md` read in full.  Shared tree vs `origin/main` for `CharClass/OddP*`: all 23 files
  byte-identical, so there was no unlanded predecessor work to rescue.
* On main: `OddPDescentWord`, `Clifford`, `Complex` (green 09-10), `Shift`, `Pairing` (compiled, gate A);
  `OddPDescentDomino`, `OddPDescentValue` landed unverified (8cdb6b3fb / e76e62198), red.
* Domino's red log: `cc_clones/cs-endpoint/.nm/build-0911-200827-98883.log` (ten errors); Value was never
  elaborated, because its import was red.

## MODEL TESTS (2026-09-11, on acn112, `nm/lix-descent/descent_levels.py`, seconds)

Conventions are exactly the Lean files': `eD = σ∧`, `eH = ∂/∂ξ₀`, `eT = ξ_j ↦ ξ_{j−1}` (sp-design's
direction), `eRound = (eT−1)∘eH∘eN∘eH`, `eX k = ξ₀∧ρ^k`, `eRoundStar = (ξ₀∧)∘eN∘(ξ₀∧)∘(eT^{p−1}−1)`.
Predicate for every line: exact equality of elements of `Λ(ξ₀,…,ξ_{p−1})` over `ℤ`, or reduced mod `p`
where it says so.

**(a) Sign vector of `N` on `v₀ = f ⊗ g^{⊗(p−1)}`** (bidegree `(0,1,…,1)`), read by the position `j` of
`f`: `N v₀ = Σ_j (−1)^j v_j` at p = 3, 5, 7, 11, 13, and the support is `p`.  (This is sp-steenrod §10's
retraction, checked here numerically.)

**(b) The primal descent at every level** (supports over `ℤ` of `A_k`, `Y1_k = H A_k`,
`Mid_k = N Y1_k`, `Y2_k = H Mid_k`):

| p | level k: \|A\| / \|Y1\| / \|Mid\| / \|Y2\| |
|---|---|
| 3 | 0: 1/1/3/2 · 1: 3/1/1/0 |
| 5 | 0: 1/1/5/4 · 1: 7/3/10/4 · 2: 5/1/1/0 |
| 7 | 0: 1/1/7/6 · 1: 11/5/28/16 · 2: 27/9/21/6 · 3: 7/1/1/0 |
| 11 | 0: 1/1/11/10 · 1: 19/9/88/64 · 2: 119/49/231/126 · 3: 225/75/220/80 · 4: 130/30/55/10 · 5: 11/1/1/0 |
| 13 | 0: 1/1/13/12 · 1: 23/11/130/100 · 2: 189/81/468/288 · 3: 532/196/728/336 · 4: 595/175/455/140 · 5: 225/45/78/12 · 6: 13/1/1/0 |

At every level and every prime: `D A_k = 0`, `D Y1_k = A_k`, `D Y2_k = Mid_k` hold **mod p**.  Over `ℤ`
they fail from level 1 on, and `D Y2_0 = Mid_0` already fails over `ℤ`: `N(ω) = p·ω`, which is the
characteristic step sp-descent's trap names.

**(c) The dual sequence closes at every level:** iterating `eRoundStar` from `ξ₀` gives exactly `ξ₀∧ρ^k` at
every `k ≤ m` (so `eX_succ` is true at every level), and `ξ₀∧ρ^k = k!·(k-domino sum)`.

**(d) Value:** `⟨A_m, ξ₀⟩ = ⟨ω, ξ₀∧ρ^m⟩ = m!` over `ℤ` on the nose: 1, 2, 6, 120, 720; mod p 1, 2, 6, 10, 5.

**(e) Interval coefficient** `[e_{1..2k}] ρ^k = k!` for every `1 ≤ k ≤ m` (`eR_pow_interval`), all five primes.

**(f) The direction trap has a closed form.**  With `eT` replaced by `eT^{−1}` the value over `ℤ` is
`−1, 2, −6, −120, 720` = **`(−1)^m·m!`**; mod p that is `2, 2, 1, 1, 5`, which matches sp-descent's table.
So the two directions differ by the sign `(−1)^{(p−1)/2}`, not by an unrelated number.  Both are units.

## FIXES (Domino, from the red log)

1. `eWedge_anticomm_apply`: `eq_neg_of_add_eq_zero_right : a + b = 0 → b = −a`, so the summands are swapped.
2. `ePart_eR_apply`: the `hsub` rewrite had nothing to rewrite (`sum_ite_eq` already yields `i − 1`); removed.
3. `ePart_eR_pow_apply`: `abel` cannot close `(n+1)•X + X = (n+1+1)•X` with `n` a variable; `succ_nsmul _ (n+1)`.
4. `eWedge_coeff_of_true` / `ePart_coeff_of_false`: inside a `rw` chain, `update_eq_self_iff.2 h.symm` is elaborated with
   its word still a metavariable, and `kabstract` picks the wrong `update`.  Stated as a `have` via
   `Function.update_eq_iff`.  `eq_update_self_iff` does not exist at the pin, so `Function.eq_update_iff` is used.
5. `eR_pow_interval`: the statement had no term fixing `p`, so `eR`'s `NeZero` problem was stuck; now `(p := p)`.  The
   body had never been elaborated.  Audited, and repaired where needed: `ring` → `omega`, `simp only` hedges →
   `Bool.eq_false_of_not_eq_true` + `omega`, the ℕ-multiple coefficient by a `have … := by simp`, and the assembly
   by `Finsupp.sub_apply` / `nsmul_eq_mul`.
6. `eT_pow_eWedge`, and `eX_succ` in Value: a bare `← Module.End.mul_apply` folds the OUTER application; the three factors are now named.
7. `eT_eR_apply`: `Fintype.sum_equiv` leaves `(Equiv.addRight 1) b` unreduced; `simp only [Equiv.coe_addRight]` (a `show` timed out, see PROBES).

Value (first elaboration ever): `simp`/`simpa` replaced by `simp only … at h; exact h`; `hp1` by `omega`;
`eTopWord_update_zero` takes no `K`, since theorem variables are included by the statement; a `def` hypothesis
(`EvalIsHeadCoeff`) is applied before rewriting; `Fin.ext` goal by `rw [h, Fin.val_zero]`; closed endpoint
`PrintedOddPDescentConstant` + `printedOddPDescentConstant` under `#audit_closed_axioms`.

## NEEDS

* **Name agreement with `lix-steenrod`, through the lead:** the export is
  `GroupApproximation.CharClass.printedOddPDescentConstant : PrintedOddPDescentConstant`.  For every odd prime `q = 2m+1`
  over `ZMod q` it gives the cocycle/primitive statements at every level, `(eA (ZMod q) m) (eHeadWord q) = m!`, and
  `IsUnit (m! : ZMod q)`.  Point-level forms: `eDescent_value` (any comm ring, no characteristic hypothesis),
  `eDescent_value_zmod`, `eDescent_value_isUnit`.
* The obligation `EvalIsHeadCoeff` (the p-fold Alexander–Whitney evaluation of a degree-one element is the head
  coefficient) is stated, not used.  It belongs to lix-steenrod's layer (`tupEval` + iterated diagonal).
  sp-descent verified it by model test at p = 3, 5, 7.

## PROBES

* 0911-215729-75941 (spare1, SLURM acn101, base a0ff25d62): Word, Clifford, Complex, Shift and Pairing were
  `Built`.  Domino's ONE remaining error: 409:2, `(deterministic) timeout at isDefEq` (200000 heartbeats), from the
  `show` in `eT_eR_apply`.  Every other Domino declaration elaborated, including `eR_pow_interval`.  Value was not
  reached.  Fix: `simp only [Equiv.coe_addRight]` instead of `show`; in Value, `eCast_pred` closed by
  `eq_neg_of_add_eq_zero_left` instead of `simpa`.

* 0911-221812-22898 (spare1, SLURM acn16): **OddPDescentDomino BUILT, COMPILED, LANDED 1a28ab8df.**  Value's first
  elaboration hit five stuck `NeZero ?p` / `OfNat (Fin ?p) 0` problems, each in a `have … := by` whose type never names
  `EMod K p`; I named `(p := p)` in seven such haves.
* 0911-222703-86070 (spare1, acn112 slot 2): **PROBE GREEN, OddPDescentValue BUILT, COMPILED, LANDED eabf84751.**
  `printedOddPDescentConstant` depends on axioms `[propext, Classical.choice, Quot.sound]`.

## GREEN

All seven `OddPDescent*` modules are compiled on main: Word, Clifford, Complex, Shift, Pairing, Domino (1a28ab8df),
Value (eabf84751).  WIRE top: `GroupApproximation.CharClass.OddPDescentValue`.

## TRAPS

* (lix-descent, 09-11) Passing `_` for the function arguments of a product-splitting lemma
  (`oddPEval_prod_split _ _ j _ hj hne`) makes Lean elaborate `hne := fun l hl => congrArg …` against `?F l = ?G l`,
  and the pattern unification `?F j =?= … update φ j ψ j …` abstracts EVERY `j`, including the one inside `update`.
  Pass `F`, `G` and the value explicitly; then `congrArg (fun ψ => tagEvalG K ψ (t.1 l)) (Function.update_of_ne hl _ φ)`
  checks against the beta-redex by defeq.  All three OddPEval* modules compiled first time with that shape.

* (lix-descent, 09-11) `have h : T := by …` where `T` fixes an implicit index only through an argument that does not
  carry it (`eY1 K k`, `eMid K k`, `ePair K (eA K m) (eX K 0)`, `eWedge K 0 …`) reports `typeclass instance problem is
  stuck NeZero ?m` (or `OfNat (Fin ?m) 0`) at the `have`.  Tactic blocks run after instance synthesis, so nothing
  from the proof can fix `p`.  A term-mode `have h : T := e` is fine when `e` fixes it.  Name it: `eY1 (p := p) K k`.
  Only the first such `have` in a proof is reported, because the proof aborts there.

* (lix-descent, 09-11) `show t` whose only change is `(Equiv.addRight 1) b` → `b + 1` inside a goal of linear-map
  applications times out at `isDefEq` (200000 heartbeats).  The same defeq passed as `exact h.symm` on single words in
  `OddPDescentShift.eT_comp_eD`, so a "defeq, therefore cheap" judgement from a neighbouring proof does not
  transfer.  Rewrite the coercion with `simp only [Equiv.coe_addRight]` (`Equiv.coe_addRight : ⇑(Equiv.addRight a)
  = fun x => x + a`, simp-normal at the pin).

* (lix-descent, 09-11) `rw [..., Function.update_eq_self_iff.2 h.symm, ...]` in a goal holding several `update`
  terms: the proof term is elaborated before `kabstract`, the word stays a metavariable, the first `update` in the
  goal is taken (a different letter), and the error blames `h` ("expected `false = w' a`").  Prove the equation
  as a `have` first.
* (lix-descent, 09-11) `abel` does not treat `n • X` with a variable `n` as linear, so `(n+1)•X + X = (n+1+1)•X`
  fails with a "Try this: abel_nf" info.  Use `succ_nsmul _ (n+1)`.
* (lix-descent, 09-11) A theorem statement whose only occurrence of the section variable `p` is inside implicit
  arguments (`eR K ^ k`, `eBot K`, `eIntervalWord i len`) leaves `p` a metavariable, and the error is
  "typeclass instance problem is stuck NeZero (?m k i)".  Name it: `(p := p)`.

## SCOPE 2 (2026-09-11 ~23:00, from lix-steenrod via the lead): the tensor evaluation layer, `CharClass/OddPEval*`

* `OddPEval.lean` — **COMPILED**, probe 0911-233304-55463 (spare1, acn112), PROBE GREEN, on main byte-identical at
  ab574afd4.  (E1) `tagEvalG`, (E2) `tupEval`, (E3) `gCoboundary` (+ `gCoboundary_zero/_succ`), `tupEval_single`,
  `tagEvalG_of_eq_zero`, `tagEvalG_zero`, `tupEval_tupUpdate_of_eq`, `tupEval_lc_tupUpdate`, (E4) `tupEval_tupD_single`,
  (E4') `tupEval_tupD_eq_zero`, (E5) `tupEval_tupT_const`, `tupEval_tupT_pow_const`, (E6) `tupEval_sum_tupT_pow`.
  Axioms `[propext, Classical.choice, Quot.sound]`.
* `OddPEvalNatural.lean` — **COMPILED**, probe 0911-235228-11757 (after OddPTupleFunctor compiled), on main
  byte-identical.  (E7) `tagEvalG_tagPush`, `tupEval_tupMap`.
* `OddPEvalMultilinear.lean` — **COMPILED**, probe 0911-235614-41211, on main byte-identical.  (E8) `tagEvalG_add`,
  `tagEvalG_smul`, `tupEval_single_update`, `tupEval_add_slot`, `tupEval_smul_slot`.
* All three probes built only their one changed module (2164 / 2174 / 2165 jobs).  Axioms `[propext, Classical.choice,
  Quot.sound]` throughout.
* WIRE tops: `GroupApproximation.CharClass.OddPEvalNatural`, `GroupApproximation.CharClass.OddPEvalMultilinear`
  (both import `OddPEval`).

## SCOPE 3 (2026-09-12, relaunch; routed from lix-steenrod): odd-primary operations. STOPPED BEFORE AUTHORING

* On 2026-09-12 the lead's stop order ended the LIX-stronger program (user ruling: LIX strengthenings are below the
  bar). It came before any `CharClass/OddPCochain*`, `OddPClasses*` or `OddPAdditive*` file was written, so nothing in
  this block was authored, probed or landed. Nothing was in flight: the tree copies of `OddPEval`, `OddPEvalNatural`
  and `OddPEvalMultilinear` are byte-identical to main, and `attic/inflight/lix-descent/` does not exist.
* Interface on main the block would use:
  * lix-steenrod's Δ0–Δ6: `OddPDiagonal.lean`, landed 7e2fb5081.
  * E1–E8 from `OddPEval*` (above).
  * `oddDiff`, `oddDiffW_castSucc`, `oddDiffS_succ`: `OddPSource`.
  * `altCoeff`: `OddPResolution`.
  * `grNorm_eq`, `grNorm_eq_grS_mul`: `OddPNorm`.
  * `cochainOfFun`, `cochainEval_cochainOfFun`: `SteenrodCochain`.
  * `cocycleClassK`, `classReprK`, `classReprK_isCocycle`, `cochainPullback_cochainCoboundaryK`,
    `cohPullbackK_cocycleClassK`: `CoeffCohomology`.
  * `cocycleClassK_add`: `CupOneComm`.
  * `Hmod`, `cohCast`, `pull`: `CohomologyBasic`.
  * `pull_eq_of_homotopyOf`: `KroneckerContractible`.
* A grep of main at tip 15fdb7443 finds none of these: `oddD`, `redPow`, or a cochain-level exactness lemma (equal
  classes ⇒ the cochains differ by a coboundary).

### Residual statements (design shapes, NEVER ELABORATED; binders may change at first compile)

Namespace `GroupApproximation.CharClass`, with the opens of `OddPDiagonal.lean`. `p` is an odd prime:
`(p : ℕ) [Fact p.Prime] (hp : Odd p)`. Degrees are `ℕ`. The generator `e_j ⊗ σ` of `W ⊗ C(X)` in degree `k` is
`Finsupp.single (⟨⟨k − j, _⟩, simplexEquiv X (k − j) σ⟩ : WSIndex k X) 1`.

**R1** (`OddPCochain`): the cochain `D_j(u) ∈ C^{pq−j}(X; F_p)`.

```lean
noncomputable def oddD (p : ℕ) [Fact p.Prime] {X : TopCat.{0}} (q j : ℕ)
    (u : singularCochainGroup (ZMod p) X q) : singularCochainGroup (ZMod p) X (p * q - j) :=
  cochainOfFun (p * q - j) fun σ =>
    tupEval (ZMod p) X p (p * q) (fun _ => Pi.single q u)
      (oddDiagApp p X (p * q)
        (Finsupp.single (⟨⟨p * q - j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,
          simplexEquiv X (p * q - j) σ⟩ : WSIndex (p * q) X) (1 : GroupRingZMod p)))
```

**R2** (the cocycle property):

```lean
theorem oddD_cocycle (p : ℕ) [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (q j : ℕ) (hj : j ≤ p * q)
    (u : singularCochainGroup (ZMod p) X q) (hu : cochainCoboundary (ZMod p) X q u = 0) :
    cochainCoboundary (ZMod p) X (p * q - j) (oddD p q j u) = 0
```

Route: evaluate at a `(pq − j + 1)`-simplex `σ'`, with `x = e_j ⊗ σ'` in degree `pq + 1`.
* By Δ1, `tupD (Δ x) = Δ (oddDiff x)`.
* `tupEval (u^{⊗p}) (tupD (Δ x)) = 0` by E4'. This needs `gCoboundary (Pi.single q u) = 0`, which follows from `hu`.
* The W-half `altCoeff (grS p) (grNorm p) _ • (e_{j−1} ⊗ σ')` dies:
  * a `grS` coefficient by Δ5 and E5;
  * a `grNorm` coefficient by Δ4 and E6, since `(p : ZMod p) = 0`.
* The S-half `(−1)^j • (e_j ⊗ ∂σ')` evaluates to `(−1)^j · δ(oddD p q j u)(σ')`.

Pushing finite sums through needs the helper
`oddEvalHom p X k φ : OddWTensor p k X →+ ZMod p := AddMonoidHom.mk' (fun x => tupEval (ZMod p) X p k φ (oddDiagApp p X k x)) (by intro x y; rw [oddDiagApp_add, map_add])`.
It works at the Finsupp, not at the ModuleCat carrier.

**R3** (naturality; no `hp`):

```lean
theorem oddD_natural (p : ℕ) [Fact p.Prime] {X Y : TopCat.{0}} (f : X ⟶ Y) (q j : ℕ)
    (u : singularCochainGroup (ZMod p) Y q) :
    cochainPullback f (p * q - j) (oddD p q j u) = oddD p q j (cochainPullback f q u)
```

Route: `cochain_ext`, `cochainPullback_eval`, Δ2, E7 (`tupEval_tupMap`), `srcMapIdx` on the generator, and `Pi.single`
commuting with the pullback (`cochainPullback_zeroOf` off degree `q`).

**R4** (a coboundary change of `u` changes the class of `D_j(u)` by nothing):

```lean
theorem oddD_coboundary (p : ℕ) [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (m j : ℕ)
    (hj : j ≤ p * (m + 1)) (u : singularCochainGroup (ZMod p) X (m + 1))
    (hu : cochainCoboundary (ZMod p) X (m + 1) u = 0) (w : singularCochainGroup (ZMod p) X m)
    (hu' : cochainCoboundary (ZMod p) X (m + 1) (u + cochainCoboundary (ZMod p) X m w) = 0) :
    cocycleClassK (ZMod p) X (p * (m + 1) - j) (oddD p (m + 1) j u)
        (oddD_cocycle p hp (m + 1) j hj u hu)
      = cocycleClassK (ZMod p) X (p * (m + 1) - j)
          (oddD p (m + 1) j (u + cochainCoboundary (ZMod p) X m w))
          (oddD_cocycle p hp (m + 1) j hj _ hu')
```

Route: a cylinder. The direct telescoping primitive `Σ_k ± tupEval(u'^k, w, u^{p−k−1})` is not `T`-invariant, so its
W-term does not die.
* Set `Y = TopCat.of (X × unitInterval)`, with `pr`, `i₀` and `i₁`.
* The homotopy `i₀ ≃ i₁` is `(t, x) ↦ (x, t)`; `map_zero_left` and `map_one_left` hold by `rfl`.
* `V = cochainOfFun (fun σ => if simplexEquiv σ = simplexEquiv (pr σ) ≫ i₁ then w (pr σ) else 0)`, and
  `U = pr^* u + δV`.
* Then `δU = 0`, `i₁^* U = u + δw`, and `i₀^* U = u`, since `Δ^m` is nonempty (`stdSimplexTop_contractibleSpace`)
  and `0 ≠ 1` in `I`.
* Conclude by R3, `cohPullbackK_cocycleClassK` and `pull_eq_of_homotopyOf`.

**R5** (`OddPClasses`): exactness, any `K`.

```lean
theorem exists_eq_add_coboundary_of_cocycleClassK_eq (K : Type) [CommRing K] (X : TopCat.{0}) (m : ℕ)
    {φ ψ : singularCochainGroup K X (m + 1)} (hφ : cochainCoboundary K X (m + 1) φ = 0)
    (hψ : cochainCoboundary K X (m + 1) ψ = 0)
    (h : cocycleClassK K X (m + 1) φ hφ = cocycleClassK K X (m + 1) ψ hψ) :
    ∃ w : singularCochainGroup K X m, φ = ψ + cochainCoboundary K X m w

theorem eq_of_cocycleClassK_eq_deg_zero (K : Type) [CommRing K] (X : TopCat.{0})
    {φ ψ : singularCochainGroup K X 0} (hφ : cochainCoboundary K X 0 φ = 0)
    (hψ : cochainCoboundary K X 0 ψ = 0)
    (h : cocycleClassK K X 0 φ hφ = cocycleClassK K X 0 ψ hψ) : φ = ψ
```

Route: the kernel of `homologyπ` is the range of `toCycles`. Mathlib at the pin has `homologyIsCokernel`
(`ShortComplex/HomologicalComplex.lean:207`), `exact_of_g_is_cokernel` and `moduleCat_exact_iff_ker_sub_range`. Combine
them with `cocycleClassK_add` and `iCycles_cyclesMkK`.

**R6** (the reduced power `P^i : H^q → H^{q+2i(p−1)}`, index `j = (q − 2i)(p − 1)`, zero when `2i > q`):

```lean
theorem redPow_deg (p : ℕ) [Fact p.Prime] (q i : ℕ) (h : 2 * i ≤ q) :
    p * q - (q - 2 * i) * (p - 1) = q + 2 * i * (p - 1)

theorem redPow_index_le (p q i : ℕ) : (q - 2 * i) * (p - 1) ≤ p * q

noncomputable def redPow (p : ℕ) [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (q i : ℕ)
    (x : Hmod (ZMod p) X q) : Hmod (ZMod p) X (q + 2 * i * (p - 1)) :=
  if h : 2 * i ≤ q then
    cohCast (redPow_deg p q i h)
      (cocycleClassK (ZMod p) X (p * q - (q - 2 * i) * (p - 1))
        (oddD p q ((q - 2 * i) * (p - 1)) (classReprK (ZMod p) X q x))
        (oddD_cocycle p hp q ((q - 2 * i) * (p - 1)) (redPow_index_le p q i)
          (classReprK (ZMod p) X q x) (classReprK_isCocycle (ZMod p) X q x)))
  else 0
```

**R7** (instability), by `dif_neg`:

```lean
theorem redPow_eq_zero_of_lt (p : ℕ) [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (q i : ℕ)
    (h : q < 2 * i) (x : Hmod (ZMod p) X q) : redPow p hp q i x = 0
```

**R8** (the computation rule on any cocycle representative):

```lean
theorem redPow_mk (p : ℕ) [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (q i : ℕ) (h : 2 * i ≤ q)
    (u : singularCochainGroup (ZMod p) X q) (hu : cochainCoboundary (ZMod p) X q u = 0) :
    redPow p hp q i (cocycleClassK (ZMod p) X q u hu)
      = cohCast (redPow_deg p q i h)
          (cocycleClassK (ZMod p) X (p * q - (q - 2 * i) * (p - 1))
            (oddD p q ((q - 2 * i) * (p - 1)) u)
            (oddD_cocycle p hp q ((q - 2 * i) * (p - 1)) (redPow_index_le p q i) u hu))
```

Route: `classReprK` of the class differs from `u` by a coboundary (R5; its degree-0 form when `q = 0`), then R4.

**R9** (`OddPAdditive`): additivity.

```lean
theorem redPow_add (p : ℕ) [Fact p.Prime] (hp : Odd p) {X : TopCat.{0}} (q i : ℕ)
    (x y : Hmod (ZMod p) X q) : redPow p hp q i (x + y) = redPow p hp q i x + redPow p hp q i y
```

Route:
* Expand `(u + v)^{⊗p} = Σ_S φ_S` with `Finset.prod_add` and E8 (`tupEval_add_slot`).
* Rotation permutes the mixed `S` freely, since `p` is prime. The sign is `+1`: every slot is in degree `q` and
  `p − 1` is even.
* This needs a new rotated-slot E5: `tupEval (ZMod p) X p k φ (tupT (ZMod p) X p k x) = tupEval (ZMod p) X p k (φ ∘ finRotate p) x`
  for `φ` with every slot concentrated in degree `q`. The rotation direction is fixed at first compile.
* Each orbit sums to `tupEval φ_{S₀} (Δ (grNorm p • (e_j ⊗ σ)))`.
* The W differential is `d e_{j+1} = altCoeff (grS p) (grNorm p) j • e_j`. So `grNorm • e_j = d e_{j+1}` for odd `j`,
  and `grNorm • e_j = d (grS^{p−2} • e_{j+1})` for even `j` (`grNorm_eq_grS_mul`).
* By Δ1 and E4' the mixed part is therefore a coboundary.
* Conclude with R8 and `cocycleClassK_add`.

Closed endpoints (`def Printed… : Prop` + `theorem printed…` under `#audit_closed_axioms`) were not stated either.

### GREEN at wind-down

* SCOPE 1: all seven `OddPDescent*` modules are compiled on main (Domino 1a28ab8df, Value eabf84751).
* SCOPE 2: `OddPEval`, `OddPEvalNatural` and `OddPEvalMultilinear` are compiled on main.
* SCOPE 3: nothing. Every statement R1–R9 is open.
