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
