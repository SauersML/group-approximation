# P13 step-for-step audit

Audit target: the P13 material of `non_mf_groups_exist.tex`, namely
`\section{The explicit presentation and its property-(T) base}`
(`\label{sec:group}`), its subsection `Property~\textup{(T)} of the base`
(Proposition `prop:literal-base-T`), Theorem `thm:p13-complete`, and
Remark `rem:classical-base`.

Standard applied (as directed): **step-for-step identity**, not architectural
agreement. Every descent step, normal-form move, Schreier calculation and Weyl
reduction, *and the order in which they are used*, must match the printed
argument. A correct shortcut is a mismatch. A stronger lemma standing where the
manuscript uses a weaker one is a mismatch. A different-but-equivalent
invariant is a mismatch.

Marks used:

* `EXACT` — same assertion, same objects, same inference, proved in Lean with
  no hypothesis standing in for mathematics.
* `MISMATCH` — Lean proves the right endpoint by a different route, a different
  invariant, a different object, or in a different order.
* `MISSING` — the printed assertion has no Lean counterpart at all.
* `UNDER-SPECIFIED` — the printed text is a prose route with no determinate
  step content to bind; the Lean supplies a proof that the sentence merely
  gestures at. Recorded separately because "EXACT" would overstate what was
  checked, and "MISMATCH" would blame Lean for the manuscript's compression.

No compilation was performed. Every mark below is from reading proof bodies,
not statements.

---

## Revision note (post-audit corrections)

Four items have moved since the first issue of this document. Two of them are
corrections to *this audit*, not to the corpus, and are recorded as such.

* **T1.04 — `MISSING` → `EXACT`. My original reading was wrong.** I observed
  correctly that the Lean route (damped Richardson/Neumann) produced a strictly
  weaker constant than the printed `1/500`, and then inferred that the printed
  spectral localization overreached and should be edited out of the TeX. That
  inference does not hold. The printed containment follows from the
  certificate's own quadratic gap **at the same constant, with no loss**:
  `Δ ≥ 0` together with `c·⟪x,Δx⟫ ≤ ‖Δx‖²` forces every spectral value to
  satisfy `λ(λ−c) ≥ 0`, hence `λ = 0` or `λ ≥ c`. It is now proved verbatim,
  on the repo's actual six-generator Laplacian with a real `spectrum ℝ`, by
  `P13SpectralGap.t1_04_p13_spectrum_subset`
  (`Monsters/P13SpectralGap.lean:294`). See §3 T1.04. **The recommended TeX
  edit is cancelled.**
* **T1.05 — `MISMATCH` → `EXACT`.** The printed *equality* `ker Δ = invariants`
  is now proved for any generating tuple:
  `P13SpectralGap.t1_05_p13_ker_eq_invariants` (line 312). TeX finding X3 is
  void.
* **X2 (`κ ≤ 1`) — downgraded.** The convention *is* printed, twice and earlier
  in the document than the point of use. See §6 X2.
* **D2 — resolved.** `Monsters/P13KernelFactorization.lean` has been deleted and
  the P13 subsystem rebuilds green. See §5 D2.

General lesson worth keeping: *"Lean's constant is worse than the paper's"* does
not imply *"the paper's constant is unsupported."* Before recommending that the
TeX move, check whether the printed claim follows from an input the repo already
has. Attempt the Lean first; recommend the TeX edit only if that attempt fails.

---

## 0. Headline verdict

The earlier "genuinely aligned" verdict **does not survive intact**, but it
fails in a narrower and more specific way than a wholesale retraction would
suggest.

1. **The kernel/completeness argument (`thm:p13-complete`) is step-for-step
   faithful**, with one genuine order inversion (§2, P13.08 vs P13.09–11) that
   is forced because *the printed order is not executable as printed*. Every
   named object in the printed route — lexicographic trajectory measure over
   the third basis column, norm-monotone normal form, the squeeze at norm one,
   conjugation through the signed-swap tail, the parabolic subgroup
   `⟨e12,e21,e31,e32⟩`, the six-coset Schreier system, powers of the block Weyl
   element, `{-1,-1} = w⁴` killed by the displayed relator — exists in Lean as
   the object of that name and is used at the place the manuscript uses it.
2. **The generated/replay layer does not bypass a manuscript step.** This is
   the crux the brief flagged, and it resolves in the Lean's favour; see §4.
   In particular the replay certifies only *equalities* between group elements,
   proved as finite products of conjugates of the thirteen displayed relators,
   and the certificate is **insensitive to whether distinct product classes are
   distinct group elements** — so no completeness or word-problem fact is
   smuggled in through the finite data.
3. **The property-(T) proof of the base (`prop:literal-base-T`) contains
   step-level mismatches**, all route substitutions rather than gaps. After the
   post-audit corrections above, Step 1 is clean and the surviving items are in
   Step 3:
   * Step 3's *"the Hilbert-space circumcenter argument"* is **MISMATCH**: Lean
     uses the minimal-norm point of the closed convex hull of the orbit (§3,
     T3.11).
   * Step 3's stated reason for omitting `v1` from the control set is
     **MISSING** from Lean, which omits `v1` for a different reason (§3, T3.04).
   * Lean uses an *isomorphism* `Rotation ≃* rotations` where the manuscript
     uses only a surjection (T3.01).
   * `κ ≤ 1` is used at the point of the `3/64` bound without being restated
     there (T3.03; downgraded — the convention is printed elsewhere).

   Step 1's two original findings — the spectral localization (T1.04) and the
   `ker Δ` equality (T1.05) — **have both been closed at the printed
   constant and in the printed form**; T1.04's original `MISSING` mark was my
   error, not a corpus defect.
4. **Two module docstrings misdescribe the development** in ways an auditor
   would be misled by; one of them advertises a route that is dead code (§5).

Nothing found is unsound. No `sorry`, no `axiom`, no `native_decide` anywhere
in the P13 corpus (`GroupApproximation/Monsters/P13*.lean`,
`GroupApproximation/Monsters/SL2*.lean`, `GroupApproximation/Monsters/SL3*.lean`,
`GroupApproximation/Sofic/LiteralP13*.lean`,
`GroupApproximation/Sofic/LiteralBaseP13*.lean`). No hypothesis in any
manuscript-facing declaration stands in for mathematics.

---

## 1. The two printed proofs, atomized

The printed material splits into two proofs. Note their very different
granularity, which determines how much the strict standard can actually bind:

* Proposition `prop:literal-base-T` is a **real proof** in three numbered
  steps with explicit constants (`κ/64`, `1/64`, `3/64`, `1/8`, `1/8+1/64<1`).
  Here the strict standard has plenty of purchase, and it is here that the
  mismatches are.
* Theorem `thm:p13-complete` is printed under `\begin{proof}[Proof route]` and
  is **seven sentences**. It names the objects and the shape of the argument
  and proves nothing. Here the strict standard binds only the named objects
  and their order; there are no intermediate inequalities, no case list, no
  measure definition to compare against. The Lean supplies ~9,700 lines against
  those seven sentences. I record that asymmetry honestly as UNDER-SPECIFIED
  rather than certifying "step-for-step identity" with steps the manuscript
  never printed.

---

## 2. Theorem `thm:p13-complete` — step ledger

Printed statement: *"The canonical homomorphism `P13 → SL_3(ℤ)`, sending each
generator `e_ij` to the corresponding elementary matrix, is an isomorphism."*
Badge: `Monsters/P13DescentMaster` /
`GroupApproximation.P13DescentMaster.p13CompletenessEquiv`.

### P13.00 — the presentation itself

TeX (Step 1 of `prop:literal-base-T`, which defines `P_13` used here): six
generators `e12,e13,e21,e23,e31,e32`, thirteen relators — six ordered Steinberg
commutators, six commuting-root commutators, `(e12 e21⁻¹ e12)⁴`.

Lean: `LiteralP13Presentation.p13RelatorLetters` (`.../Sofic/LiteralP13Presentation.lean:36`).
Checked letter by letter against the display:

| TeX relator | Lean index | Lean signed word | match |
|---|---|---|---|
| `[e12,e23]=e13` | 0 | `(0+)(3+)(0-)(3-)(1-)` | yes |
| `[e13,e32]=e12` | 1 | `(1+)(5+)(1-)(5-)(0-)` | yes |
| `[e21,e13]=e23` | 2 | `(2+)(1+)(2-)(1-)(3-)` | yes |
| `[e23,e31]=e21` | 3 | `(3+)(4+)(3-)(4-)(2-)` | yes |
| `[e31,e12]=e32` | 4 | `(4+)(0+)(4-)(0-)(5-)` | yes |
| `[e32,e21]=e31` | 5 | `(5+)(2+)(5-)(2-)(4-)` | yes |
| `[e12,e13]=1` … `[e31,e32]=1` | 6–11 | six four-letter commutators, in the printed order `12_13, 12_32, 13_23, 21_23, 21_31, 31_32` | yes |
| `(e12 e21⁻¹ e12)⁴=1` | 12 | `((0+)(2-)(0+))×4` | yes |

Generator indexing `0..5 = e12,e13,e21,e23,e31,e32` is fixed at
`LiteralP13Presentation.lean:10-15` and is the same indexing used by the matrix
model, the descent letters, and the Hodge certificate.
**EXACT.**

### P13.01 — "The canonical homomorphism … sending each generator `e_ij` to the corresponding elementary matrix"

Lean: `LiteralP13MatrixModel.elem` (six `1+E_ij` matrices, in the printed order)
and `toSL3 := PresentedGroup.toGroup …`, with
`lift_elem_relator_eq_one` killing all thirteen relators by kernel `decide` on
closed `3×3` integer identities (`Monsters/LiteralP13MatrixModel.lean:35,45,59`).
**EXACT.**

### P13.02 — "Surjectivity is Euclidean elimination."

Lean: `SL3ElementaryGeneration.toSL3_surjective`
(`Monsters/SL3ElementaryGeneration.lean:625`), via `mem_H` (line 344) built from
`pair_reduce` (line 198), which is strong induction on `Int.natAbs` of an entry
with `emod_shrink` (line 184) — literally the Euclidean algorithm on a pair of
rows, with the signed swap `sw` (line 130) realized as a three-transvection
word and every transvection an integer power of a displayed elementary matrix
(`tv_mem`, line 92). Two column stages and two row stages reduce to a sign
diagonal; each sign diagonal is the square of a signed swap (`sw_sq_01/02/12`).
**EXACT.**

### P13.03 — "Injectivity is the unstable `K₂(3,ℤ)=ℤ/2` computation in presentation form"

Framing sentence. The Lean chain is
`toSL3_injective` ← `toSL3_ker_eq_bot descent_normal_form`
(`Monsters/P13DescentMaster.lean:2581`, `Monsters/P13Completeness.lean:175`),
i.e. injectivity is proved as kernel triviality of the presentation map, and
the only place `ℤ/2` enters is `w23_sq` / `w_pow_four` (P13.11).
**EXACT** (as framing).

### P13.04 — "every word in unit root letters normalizes, by a descent on the lexicographic measure of its trajectory over the third basis column, into a norm-monotone word times an element of the signed-swap subgroup `⟨w13,w23⟩`"

Lean: `P13DescentMaster.descent_normal_form` (line 2547):

```
∃ G mon, mon ∈ Subgroup.closure {w13, w23} ∧
  eval W = eval G * mon ∧ Mono G (act (toSL3 mon) e3)
```

Checked in detail, because this is where a substitution would be easiest to
hide:

* *"word in unit root letters"* — `UnitWord W : ∀ l ∈ W, l.2 = 1 ∨ l.2 = -1`,
  letters `Letter = Fin 6 × ℤ`, `letterVal (i,c) = (e_i)^c`
  (`P13DescentCore.lean:41,44,62`). Every element of `P13` is such a word:
  `exists_word` (line 66). **Same objects.**
* *"trajectory over the third basis column"* — `e3 = ![0,0,1]`
  (`P13ColumnLift.lean:40`), `act` is the honest `mulVec` column action
  (line 52). The descent invariant carries the base column
  `b = act (toSL3 mon) e3`, which at first sight looks like a *moving* base and
  therefore a different invariant from the printed one. It is not:
  `vecOf W b = act (toSL3 (eval W)) (act (toSL3 mon) e3)
             = act (toSL3 (eval W * mon)) e3`,
  so `sigma V b j` is exactly the ℓ¹ norm of the `j`-th suffix of the **whole**
  word `V·mon` applied to `e₃`. The Lean invariant *is* the trajectory over the
  third basis column. **Same invariant** — I flag this explicitly because it is
  the one place where a reader could wrongly record a mismatch.
* *"lexicographic measure"* — `meas W b = (lam W b, W.length - topViol W b)`
  in `Prod.Lex` (`P13WordDescent.lean:174`), `lam` the largest violated height
  (line 129), `topViol` the least position attaining it (line 156). The
  manuscript names the measure "lexicographic" and does not say which pair; the
  Lean pair is a determinate choice the manuscript leaves open.
  **UNDER-SPECIFIED** at this sub-point.
* *"norm-monotone"* — `Mono` (`P13DescentCore.lean:194`): reading the word
  right-to-left, no letter decreases the trajectory norm. `mono_iff_no_viol`
  (`P13WordDescent.lean:68`) ties it to the absence of violations, and the
  induction terminates exactly when no violation remains
  (`descent_normal_form`, line 2576–2578).
* The induction is `WellFounded.prod_lex Nat.lt_wfRel.wf Nat.lt_wfRel.wf`
  (line 2563) — a genuine lexicographic descent, one `descent_step` per round.

The single descent step, `descent_step` (line 1446), splits at the topmost
worst violation (`word_split`, line 39; `viol_succ_lt`, line 81;
`side_le_of_top`, line 96) and does a complete `fin_cases i <;> fin_cases ip`
over all **36** ordered letter-family pairs. I counted the case bullets: 36,
with no catch-all, no `all_goals`, no admitted branch. The class table matches
the one documented at `P13DescentCases.lean:21-35`: same family (cancellation;
aligned pair impossible at a violation), same read `{0,5},{1,3},{2,4}` (swap
cuts the peak), same write `{0,1},{2,3},{4,5}` (swap or one of two conjugation
sandwiches), Steinberg `(0,3),(1,5),(2,1),(3,4),(4,0),(5,2)` and reversals
(one of three split orders, or the block-Weyl emission), braid `{0,2},{1,4},{3,5}`
(anti-aligned only, one-letter emission). Identity lemmas come from the
Steinberg calculus (`P13SteinbergCalculus.lean`, every relation derived from the
thirteen relators via `conj_engine`, line 179 — no matrix model); existence
lemmas are sign-case splits closed by `omega` over the explicit coordinate
action (`act_x0`…`act_x5`).

Verdict: **EXACT** on every named object; **UNDER-SPECIFIED** on the interior,
which the manuscript does not print at all. Nothing in the 36-case table
contradicts the printed sentence, and nothing in it is a shortcut around it.

### P13.05 — "For a kernel word the monotone trajectory is squeezed at norm one"

Lean: inside `toSL3_ker_eq_bot` (`P13Completeness.lean:187-192`):
`htop : vecOf G b = act (toSL3 (eval W)) e3`, then `hg : toSL3 (eval W) = 1`
gives `htop1 : vnorm (vecOf G b) ≤ 1`; `hbc : IsCorner b` from
`isCorner_of_closure` (line 165), so the base has norm one too
(`vnorm_corner`). **EXACT.**

### P13.06 — "so every letter fixes the base column"

Lean: `P13DescentCore.letters_fix_of_mono` (line 338), whose engine is
`corner_fix` (line 222): a letter that keeps the norm of a *corner* at one
fixes that corner — proved by exhausting the six root families and the six
signed basis columns with `simp_all [vnorm]`. Note the Lean says "base column",
not "`e₃`", and the base column here is the corner `b = act (toSL3 mon) e3`,
which is exactly what the manuscript's "the base column" denotes.
**EXACT.**

### P13.07 — "conjugating through the signed-swap tail lands the word in the parabolic subgroup `⟨e12,e21,e31,e32⟩`"

Lean: `exists_conj_letter_map` (`P13Completeness.lean:92`) produces a letter
permutation `f` with `mon⁻¹ · letterVal l · mon = letterVal (f l)` by closure
induction on `⟨w13,w23⟩` from the two explicit inverse-conjugation tables
`w13ConjInv`, `w23ConjInv` (lines 37,46) and their proofs from
`w13_conj_letter`, `w23_conj_letter`. Then `hconj` (line 196) pushes the whole
word across, `hfix'` (line 207) shows every conjugated letter fixes `e₃`, and
`eval_mem_Hpar_of_all_fix` (`P13DescentCore.lean:297`) lands
`eval (G.map f) ∈ Hpar`.

`Hpar = Subgroup.closure parGens`, `parGens = {of 0, of 2, of 4, of 5}`
(`P13ParabolicKernel.lean:32`) = `{e12, e21, e31, e32}` — the printed generating
set, in the printed order. **EXACT.**

The per-letter step `letter_mem_Hpar_of_fix` (`P13DescentCore.lean:259`) is
sharper than the printed sentence and correctly so: for the two non-parabolic
families `e13`, `e23`, fixing `e₃` forces the *exponent* to vanish.

### P13.08 — "whose elements the matrix model separates by their semidirect normal form"

Lean: `P13ParabolicKernel.exists_parabolic_form` (line 174) — every element of
`Hpar` is `x31(a)·x32(b)·sl2ToP13 γ`, i.e. `N ⋊ Γ` with `N = ⟨e31,e32⟩`
(`Nsub`, line 94) normalized by the rank-two block `Γ = ⟨e12,e21⟩`
(`block_mem_normalizer`, line 139) — and
`eq_one_of_mem_parabolic_of_map_eq_one` (line 239) reads `γ` off the top-left
`2×2` block and then `(a,b)` off the bottom row, exactly as the printed clause
says. **EXACT** as to route.

**Ingredient absent from the manuscript.** The separation needs the block
`Γ` to be faithful, i.e. `SL2Completeness.toSL2_injective`
(`Monsters/SL2Completeness.lean:236`) — completeness of the rank-two braid
presentation `⟨a,b | aba=bab, (aba)⁴⟩`, proved by mapping to `ℤ/2 ∗ ℤ/3`
(`alpha`, line 89), comparing with the Möbius ping-pong embedding
(`psi_comp_alpha`, line 174) and with the quotient by `⟨s²⟩`
(`gamma_comp_alpha`, line 144), then killing the residual central power. That
is a substantial theorem with its own ping-pong argument, and the manuscript
does not mention it at any point. It is required to make the printed clause
true, so this is manuscript under-specification, not a Lean defect — but it
means the printed six-word clause "the matrix model separates them by their
semidirect normal form" is carrying a ping-pong argument in `ℤ/2 ∗ ℤ/3`.
**UNDER-SPECIFIED.**

### P13.09/P13.10 — "the signed-swap subgroup … is governed, over ℤ, by a six-coset Schreier system whose every Schreier element is a power of the block Weyl element"

Lean: `P13MonomialMachine` — six coset representatives
`repw : Fin 6 → P13` (line 239) in the printed orbit order
`e₃ ↦ 1, e₁ ↦ w13, e₂ ↦ w23, -e₃ ↦ w13², -e₁ ↦ w13³, -e₂ ↦ w23·w13²`
(the module docstring, line 15, states this orbit list explicitly);
`wpow : Fin 4 → P13` the powers of the block Weyl element `w = w₁₂`
(line 257); the **twelve** Schreier steps `w13_mul_repw` (line 325) and
`w23_mul_repw` (line 357), each of the form `w_• · repw j = repw j' · wpow k`;
and the normal form `exists_rep_wpow` (line 500) by left closure induction.
Every Schreier element produced is `wpow k`, i.e. a power of `w`
(`wpow_mem_Hpar`, line 263). The endgame `mem_Hpar_of_stab` (line 541) then says
a signed-swap element whose matrix fixes `e₃` has `repVec j = e₃`, forcing
`j = 0` and leaving a bare power of `w`. Six cosets, twelve steps, all Schreier
elements powers of the block Weyl element — precisely the printed sentence.
**EXACT.**

### P13.11 — "the classical obstruction `{-1,-1}=w⁴` is killed by the displayed relator"

Lean: `P13WeylCalculus.w_pow_four` (line 230) is literally relator 12:
`E12 * E21⁻¹ * E12 = w` by definition, so `w⁴ = 1` is
`weyl_fourth_power` = the displayed relator
(`P13SteinbergCalculus.lean:116`). The other two fourth powers are transported
by the signed transposition identity `(23) = (13)(12)(13)`
(`P13WeylFourthPowers.w13_conj_w`, line 24). The `{-1,-1}` residue appears where
the manuscript places it: `w23_sq : w23² = w²·w13²`
(`P13MonomialMachine.lean:192`), documented in-place as *"the residue of the
classical `{-1,-1}` computation, closed by the killed fourth power"*, and it is
exactly the identity that makes the six-coset table close (used at
`w23_mul_repw` cases 2 and 5). **EXACT.**

### P13.12 — "and with it the kernel"

Lean: `toSL3_ker_eq_bot` (`P13Completeness.lean:175`), assembling
`hsplit : eval W = mon * eval (G.map f)` (line 221), `hmonstab` (line 225),
`hmonH := mem_Hpar_of_stab hmon hmonstab` (line 242),
`hWH : eval W ∈ Hpar` (line 243), then
`eq_one_of_mem_parabolic_of_map_eq_one hWH hg`. **EXACT** as to content.

### P13.ORDER — the one genuine order inversion

Printed order:

> (07) conjugating through the signed-swap tail lands the word in the parabolic
> subgroup, (08) whose elements the matrix model separates by their semidirect
> normal form. (09–11) The signed-swap subgroup itself is governed … by a
> six-coset Schreier system … the classical obstruction is killed …, (12) and
> with it the kernel.

Lean order: 07 → 09/10 (Schreier: `mon ∈ Hpar`) → 12a (`eval W ∈ Hpar`) → 08
(separation applied last, to `eval W`).

This is a real deviation from the printed sequence, and it is **forced**: the
printed order applies the separation clause (08) to the conjugated word
`G.map f` *before* the tail has been placed, but `G.map f` is **not** in the
kernel — `toSL3 (eval (G.map f)) = (toSL3 mon)⁻¹`, not `1`
(`P13Completeness.lean:226-235`) — so `eq_one_of_mem_parabolic_of_map_eq_one`
cannot be invoked there. The separation can only be applied after the Schreier
endgame has put `mon` in `Hpar` and the two halves have been recombined.

**MISMATCH (order), with the defect on the TeX side.** The printed route is not
executable in the order printed; the Lean order is the only one that closes.
This is worth recording as a TeX finding, not a Lean one.

### P13.13 — "is an isomorphism"

`p13CompletenessEquiv := MulEquiv.ofBijective toSL3 ⟨toSL3_injective,
SL3ElementaryGeneration.toSL3_surjective⟩` (`P13DescentMaster.lean:2587`).
Badge target matches. **EXACT.**

### Remark `rem:classical-base`

`LiteralBaseCompleteness.baseAffineEquiv : Base ≃* gammaBar`
(`Monsters/LiteralBaseCompleteness.lean:922`), assembled from the semidirect
skeleton plus `P13DescentMaster.toSL3_injective` on the rotation factor and the
`v1^a v2^b v3^c` normal form on the translation factor. Shape matches the
printed remark. **EXACT** (not audited line-by-line; outside the P13 core).

---

## 3. Proposition `prop:literal-base-T` — step ledger

Badge: `Sofic/LiteralBaseP13PropertyTBridge` /
`GroupApproximation.LiteralBaseP13PropertyTBridge.manuscriptBaseHasKazhdanPropertyT`.

### Step 1 — the certified Steinberg-type presentation

**T1.01** *the thirteen relators of `P_13`* — see P13.00. **EXACT.** Additionally
`ManuscriptP13Presentation` (`Sofic/LiteralP13HodgeCertificate.lean:19`) pins
each relator letter-list and each generator name by `rfl`, so a later edit to
the presentation breaks this theorem rather than silently re-badging. Good
practice; matches the printed display exactly.

**T1.02** *"An exact sum-of-squares certificate with integer matrix data,
verified by denominator-free rational arithmetic, proves the degree-one Hodge
estimate for `P_13` with spectral gap `1/500`."*

Lean: `cleanP13Certificate : Certificate D B q R (1/250) (1/500)`
(`LiteralP13HodgeCertificate.lean:216`) and
`p13_hodge_gap : (1/500) * familyNormSq z ≤ matrixEnergy rho (hodgeMatrix D B) z`
(line 231). The gap delivered is `c - r = 1/250 - 1/500 = 1/500`. ✓ the printed
constant.

* "integer matrix data": `qNumerator : Fin 102 → Fin 6 → Fin 22 → ℤ`
  (`LiteralP13HodgeData.lean:~1040`), a `102×6×22` exact integer table at
  denominator `10⁸`.
* "denominator-free rational arithmetic": the ℓ¹ checks are `ℕ` identities on
  integer numerators at the common denominator `10¹⁶`
  (`residual_block_natAbs`, `LiteralP13HodgeCertificate.lean:127`;
  `residual_row_bound` / `residual_column_bound`, lines 175, 182), the 36 block
  totals coming from 144 kernel `decide` computations
  (`LiteralP13HodgeResidual{ik}Part{p}.lean`).
* `Certificate` (`Kazhdan/ExactHodgeCertificate.lean:490`) is a `Prop`
  structure whose five fields are all finite identities/inequalities
  (`gap_pos`, `chain`, `decomposition`, two ℓ¹ bounds). No field is an
  assumption standing in for mathematics. `chain` is proved from the Fox
  telescoping identity plus the defining relation
  (`LiteralP13HodgeData.chain`, line 54).

**EXACT.**

**T1.03** *"Testing it on coboundaries gives, in every orthogonal
representation, the quadratic gap `‖Δξ‖² ≥ (1/500)⟨Δξ,ξ⟩` for the
six-generator Laplacian `Δ`."*

Lean: `p13_generatorLaplacian_quadratic_gap` (line 241):
`(1/500) * PositiveOperatorGap.energy (generatorLaplacianOperator p13Generator rho) x
 ≤ ‖generatorLaplacianOperator p13Generator rho x‖^2`, where
`energy A x = ⟪x, A x⟫_ℝ` (`PositiveOperatorGap.lean:20`). The proof
(`Certificate.generatorLaplacian_quadratic_gap`,
`ExactHodgeCertificate.lean:782`) literally *tests the Hodge form on the
coboundary family* `z i = evaluate rho (generatorCoboundary s i) x` and rewrites
by `matrixEnergy_hodge_coboundary_eq` — i.e. the printed "testing it on
coboundaries", not a re-derivation. Six generators: `p13Generator : Fin 6 → P13`.
**EXACT.**

**T1.04** *"The gap places the spectrum of `Δ` in `{0}∪[1/500,∞)`."*

**EXACT.** *(Originally marked `MISSING`; that mark was my error — see the
revision note.)*

`P13SpectralGap.t1_04_p13_spectrum_subset` (`Monsters/P13SpectralGap.lean:294`)
proves

```
spectrum ℝ (generatorLaplacianOperator p13Generator rho) ⊆ {0} ∪ Set.Ici (1/500)
```

for an arbitrary orthogonal representation `rho` of `P13` — the printed
sentence, on the printed operator, at the printed constant, with a real
`spectrum ℝ` rather than a surrogate. It is discharged from the abstract
`spectrum_subset_zero_union_Ici` (line 228) by supplying exactly three inputs
the certificate already has: symmetry (`generatorLaplacian_symmetric`),
positivity of the form (`generatorLaplacian_energy` plus `sq_nonneg`), and
T1.03's quadratic gap (`p13_generatorLaplacian_quadratic_gap`). No `sorry`, no
`axiom`, no `native_decide`; the two supporting lemmas
(`norm_sub_smul_lower_bound`, line 158, and
`isUnit_of_isSymmetric_of_lower_bound`, line 193) are proved in the same file.

**Why my original reading was wrong.** I observed correctly that the route then
in place — `PositiveOperatorGap.norm_le_of_quadratic_gap`
(`Kazhdan/PositiveOperatorGap.lean:106`), a damped Richardson iteration
`T = I − M⁻¹A` whose docstring says outright that it *"does not rely on a
complex spectral theorem"* — yields only
`‖x‖ ≤ (c(1 − √(1 − c/M)))⁻¹‖Ax‖`, with `M = max(c, 4·6) = 24`, a constant
some five orders of magnitude worse than `1/500`. From that I inferred that the
printed spectral claim was stronger than the argument supports and recommended
editing the TeX. The inference is invalid: the weak constant is an artifact of
the *iteration*, not a ceiling on the *mathematics*. The containment is a
one-line consequence of positivity plus the quadratic gap — `Δ ≥ 0` and
`c⟪x,Δx⟫ ≤ ‖Δx‖²` force `λ(λ−c) ≥ 0` on the spectrum — and is therefore
sharp-constant. The exact certificate in fact supports a true gap of
`c − r = 1/250 − 11670886519714/10¹⁶ ≈ 1/353`, so the printed `1/500` is
conservative, not optimistic.

The Richardson development is untouched and still drives
`Certificate.isKazhdanPair`. `Monsters/P13SpectralGapNorm.lean` shows what it is
for: it supplies invertibility, after which the printed constant is recovered
exactly (`p13_spectrum_subset_Ici`, line 265). That file also records a nuance
worth keeping — the containment `spectrum ⊆ {0} ∪ [c,∞)` alone does *not*
exclude `0` from the spectrum, it only makes `0` isolated; excluding `0`
requires the no-invariant-vector hypothesis, and the printed sentence passes
over that.

**T1.05** *"The kernel of `Δ` is exactly the space of invariant vectors."*

**EXACT.** *(Originally marked `MISMATCH`, on the ground that only one inclusion
was proved.)* `P13SpectralGap.t1_05_p13_ker_eq_invariants`
(`Monsters/P13SpectralGap.lean:312`) now proves the printed set equality

```
{x | generatorLaplacianOperator p13Generator rho x = 0} = {x | ∀ g, rho g x = x}
```

from `ker_generatorLaplacian_eq_invariants` (line 263), stated for an arbitrary
generating tuple. The nontrivial inclusion is still
`invariant_of_generatorLaplacian_eq_zero`
(`Kazhdan/ExactHodgeCertificate.lean:734`); the converse is the observation that
a fixed vector kills every summand of `∑ᵢ‖ρ(sᵢ)x − x‖²`. The Kazhdan argument
continues to consume only the one inclusion, but the printed equality is no
longer an unproved assertion.

**T1.06** *"Hence a unit vector almost fixed by the six generators has small
Laplacian energy and is close to an invariant vector."*

**MISMATCH.** The Lean route is the dual formulation: `Certificate.isKazhdanPair`
(`ExactHodgeCertificate.lean:846`) works inside a representation with **no**
invariant vectors (`hno`), derives the lower bound on `Δ`, and concludes that
some generator moves `x` by at least `ε‖x‖`. It never produces a nearby
invariant vector, and `IsKazhdanPair` itself (`Kazhdan/Kazhdan.lean:21`) asserts
only *"has a nonzero invariant vector"* — not *"close to an invariant vector"*.
The two formulations are equivalent for property (T), which is why nothing
breaks, but the printed sentence has no Lean counterpart at this node. (The
moving-projection form the sentence describes does exist in the repo and *is*
used, but one step later, in Step 3 item 1 — see T3.05.)

**T1.07** *"This yields a Kazhdan pair: `P_13` has property (T)."*

Lean: `Certificate.hasKazhdanPropertyT` (line 968) with explicit pair
`(generatorFinset p13Generator, certifiedKazhdanTolerance 6 (1/250) (1/500))`;
instantiated at `p13_hasKazhdanPropertyT` (`LiteralP13HodgeCertificate.lean:250`)
using `closure_range_p13Generator`. Explicit finite set, explicit positive
tolerance. **EXACT.**

### Step 2 — the explicit surjection onto the linear presentation

**T2.01** *the six substitution words.* Checked character by character against
`LiteralBaseP13RotationQuotient.lean:43-54` (uppercase = inverse, via
`rotationSignedWord`):

| TeX | Lean string | reading |
|---|---|---|
| `e12 ↦ y⁻¹xzy⁻¹x⁻¹` | `"YxzYX"` | ✓ |
| `e13 ↦ xzy⁻¹x⁻¹y` | `"xzYXY"` | ✓ |
| `e21 ↦ y⁻¹xyxz` | `"Yxyxz"` | ✓ |
| `e23 ↦ x⁻¹y⁻¹xzy⁻¹` | `"XYxzY"` | ✓ |
| `e31 ↦ xy⁻¹xzy⁻¹x` | `"xYxzYx"` | ✓ |
| `e32 ↦ x⁻¹zy⁻¹x⁻¹y⁻¹x⁻¹` | `"XzYXYX"` | ✓ |

**EXACT.**

**T2.02** *"A word-by-word verification inside `R`, using only its eight
displayed relators, checks that all thirteen relators of `P_13` map to the
identity."*

Lean: `p13RelatorRotationWord_image_eq_one` (line 98), thirteen cases discharged
by the replay modules `S123 … S321`, `O12_13 … O31_32`, `Torsion`. Each is a
chain of `rotationStep` invocations (`Sofic/LiteralBaseP13RotationReplay.lean:45`),
and each `rotationStep` is **one** conjugated insertion/deletion of **one** of
the eight displayed rotation relators, verified in the free group by `decide`
and mapped through `mk_eq_mk_of_replay`. That is literally a word-by-word
verification using only the eight displayed relators — the printed sentence,
mechanized. The eight relators (`LiteralBaseRotationRetract.lean:30-39`) match
`eq:sl3presentation` exactly (`x³, y³, z², (xz)³, (yz)³, (x⁻¹zxy)², (y⁻¹zyx)²,
(xy)⁶`). **EXACT.**

**T2.03** *"The same computation exhibits explicit words in the six images whose
values are `z` and `xy`."* — `p13ZPreimage_image`, `p13XYPreimage_image`
(lines 167, 182), with explicit `FreeGroup P13Generator` preimages and replay
proofs. **EXACT.**

**T2.04** *"A further computation shows that `z` and `xy` generate `R`."* —
`LiteralBaseP13Replay.closure_Z_XY_eq_top` (line 142), from `yFromUZXY_eq`
(line 130), a 31-relator-insertion trace recovering `Y` from `Z` and `X·Y`.
**EXACT.**

**T2.05** *"Hence the homomorphism is surjective."* — `p13ToRotation_surjective`
(line 197). **EXACT.**

**T2.06** *"Property (T) passes to quotients, so `R` has property (T)."* —
`HasKazhdanPropertyT.of_surjective` (`Kazhdan/Kazhdan.lean:268`), applied at
`LiteralBaseP13PropertyTBridge.lean:28`. **EXACT.**

### Step 3 — the fixed-point bridge to the base

**T3.01** *"The generators `x,y,z` of `B` satisfy the relators of `R`, so `R`
maps to the linear subgroup of `B` they generate."*

**MISMATCH (strengthening).** Lean does prove the printed half —
`rotationGeneratorToBase_kills` (`LiteralBaseRotationRetract.lean:137`) and
`rotationToBase` (line 159), with `rotationToBase_range = rotations` (line 256).
But the property-(T) transfer at
`LiteralBasePropertyTBridge.lean:210-211` is performed by
`HasKazhdanPropertyT.of_mulEquiv rotationEquivRotations.symm`, i.e. through an
**isomorphism** `Rotation ≃* rotations` (line 368), whose injectivity half needs
the retraction `baseToRotation` (line 189) and
`rotationToBase_injective` (line 233). The manuscript claims only a map, and
`HasKazhdanPropertyT.of_surjective` — used two lines earlier for the
`P13 ↠ Rotation` transfer — would have discharged the printed step directly.
So a strictly stronger fact, with its own supporting module, stands where the
manuscript uses a weaker one. Sound, but not the printed step.

**T3.02** *"Step 2 gives a finite set `S` of words in `x,y,z` and a `κ>0`
forming a Kazhdan pair for it."* — `hRotations.exists_identity_pair`
(`LiteralBasePropertyTBridge.lean:212`) yields `S : Finset rotations`, `κ`.
**EXACT.**

**T3.03** *"…a unit vector `ξ` displaced by less than `κ/64` by every element of
the finite control set consisting of `S` together with the translations
`v₂, v₃`."*

Lean: `baseControlSet S = (S.image ↑) ∪ {v2, v3}` (line 38), tolerance `κ/64`
(line 214). Set and constant match exactly. **EXACT**, with one caveat:
`exists_identity_pair` also supplies `hkappaOne : κ ≤ 1`, which the Lean *uses*
(at `hkappa64`, line 138, hence in T3.09) but the manuscript never states.
Harmless — any Kazhdan constant may be shrunk — but it is an unstated
normalization on which the printed constant `3/64` depends. **Minor gap in the
TeX.**

**T3.04** *"The third basis translation needs no separate control: `v₁ = xv₂x⁻¹`
by the displayed `x`-action, and conjugation by the fixed unitary of `x`
preserves displacements of vectors fixed by the linear subgroup."*

**MISSING.** There is no Lean counterpart to this sentence, and it is not used.
Lean omits `v₁` from the control set for a *different* reason: the two-conjugate
normal form (T3.07) expresses **every** lattice element — `v₁` included — as
`r v₃ r⁻¹ · s v₂ s⁻¹`, so `norm_translation_displacement_le_of_rotations_fixed`
(`Sofic/LiteralTranslationOrbit.lean:456`) bounds *all* translations by
`‖ρv₃p − p‖ + ‖ρv₂p − p‖` and `v₁` never needs a bound of its own. The printed
justification (`v₁ = xv₂x⁻¹`, plus conjugation-invariance of the displacement of
a linear-fixed vector) is a correct but *distinct* argument that Lean does not
make. Under the governing standard this is a printed step with no Lean image.

**T3.05** *(item 1)* *"Projecting `ξ` to the subspace of vectors fixed by the
linear subgroup gives such a fixed vector `p` with `‖p−ξ‖<1/64`, by the
moving-projection estimate for the Kazhdan pair."*

Lean: `movingProjection_norm_lt_one_div_sixtyFour`
(`LiteralBasePropertyTBridge.lean:73`) — `KazhdanFixedSpace.subgroupMovingProjection`,
`exists_moved_mul_norm_of_noInvariant` on the moving subspace,
`norm_subgroupMovingProjection_displacement_le_of_mem_normalizer`, closing with
`κ‖m‖ ≤ ‖ρq m − m‖ ≤ ‖ρq x − x‖ < κ/64`. Same object (the moving projection),
same estimate, same constant `1/64`. **EXACT.**

**T3.06** *(item 2)* *"Three explicit words in `x,y,z` act on the translation
lattice as elementary transvections."*

Lean: `e13 = x z y⁻¹ x⁻¹ y⁻¹`, `e23 = x⁻¹ y⁻¹ x z y⁻¹`,
`e32 = x⁻¹ z y⁻¹ x⁻¹ y⁻¹ x⁻¹` (`LiteralTranslationOrbit.lean:31-37`), with the
transvection action proved *inside the presentation*: `e13_conj_v3 = v1·v3`,
`e23_conj_v3 = v2·v3`, `e32_conj_v2 = v2·v3`, plus the three fixings
(lines 135–228). Three words, `E₁₃`, `E₂₃`, `E₃₂` as named. **EXACT.**

**T3.07** *"Consequently every lattice element is a product of two
linear-subgroup conjugates of basis translations — a two-conjugate normal form
proved inside the presentation."*

Lean: `latticeTranslation_eq_two_rotation_conjugates` (line 338):
`latticeToBase a = r v₃ r⁻¹ · s v₂ s⁻¹` with `r = e13^m e23^n`,
`s = e32^k`, `m = a₀`, `n = a₁ − 1`, `k = a₂ − 1`. Exactly two conjugates,
uniformly in the lattice coordinates; every equality proved in `Base`.
**EXACT.**

**T3.08** *"A conjugate `rvr⁻¹` with `r` in the linear subgroup displaces the
fixed vector `p` exactly as much as `v` does."* — `norm_conjugate_displacement_eq`
(line 433), an equality, as printed (not an inequality). **EXACT.**

**T3.09** *"Each control translation displaces `p` by less than `3/64`, because
its displacement bound at `ξ` transfers across `‖p−ξ‖`."*

Lean: `norm_displacement_at_near` (line 54):
`‖ρg p − p‖ ≤ ‖ρg x − x‖ + 2‖p − x‖ < κ/64 + 2/64 ≤ 3/64` (`hv2p`, `hv3p`,
lines 143, 147). The transfer mechanism is exactly the printed one.
**EXACT** (modulo the `κ ≤ 1` caveat of T3.03).

**T3.10** *"Hence every translation displaces `p` by at most `1/8`."* —
`htranslation` (line 151) from `norm_translation_displacement_le_of_rotations_fixed`:
`≤ 3/64 + 3/64 = 3/32 ≤ 1/8`. **EXACT.**

**T3.11** *(item 3)* *"The orbit of `p` under the translation subgroup is
bounded, so the Hilbert-space circumcenter argument gives a translation-fixed
vector `q` with `‖q−p‖ ≤ 1/8`."*

**MISMATCH (method).** Lean uses
`HilbertConvexFixedPoint.exists_near_fixedSubspace` (line 110), whose engine
`exists_fixed_of_orbit_displacement_le` (line 78) takes the **minimal-norm point
of the closed convex hull of the orbit** (`exists_norm_eq_iInf_of_complete_convex`,
uniqueness by `eq_of_norm_eq_iInf`, line 58), then shows the hull lies in
`closedBall p δ`. That is the Hilbert projection / Bruhat–Tits construction, not
the circumcenter (the centre of the smallest enclosing ball). Both are standard,
both give `‖q − p‖ ≤ 1/8` here, but the printed step names a different
construction. The module docstring is candid about this
(`"proved from the Hilbert projection theorem: the closed convex hull of a
bounded orbit has a unique point of least norm"`).

**T3.12** *"the orthogonal projection `η` of `p` to the translation-fixed
subspace is the nearest fixed vector, so `‖η−p‖ ≤ ‖q−p‖ ≤ 1/8`."*

Lean: `hyp` (`LiteralBasePropertyTBridge.lean:181-193`), via
`Submodule.starProjection_minimal` and `ciInf_le` at the witness `z`.
Nearest-point property used exactly as printed. **EXACT.**

**T3.13** *"The linear subgroup normalizes the translation subgroup and fixes
`p`, so `η` is fixed by it as well."* — `hRotNormalizes` (line 162) from
`normalizer_translations_eq_top`, then
`KazhdanFixedSpace.fixedProjection_eq_sup_of_fixed_of_normalizes` (line 168).
Both printed hypotheses (normalizes, fixes `p`) are exactly the two hypotheses
of the Lean lemma. **EXACT.**

**T3.14** *"Translations and the linear generators generate `B`, so `η` is
`B`-invariant."* — `translations_sup_rotations` rewritten to `⊤` (line 179),
`hyGlobal` (line 175). **EXACT.**

**T3.15** *"Finally, `‖η−ξ‖ ≤ 1/8+1/64<1` keeps `η` nonzero."* — the final
`calc` at lines 195–198, then `hy : y ≠ 0` at line 218 from `‖x‖ = 1`.
**EXACT**, same decomposition, same two constants.

**T3.16** *"…`B` has property (T) in the real-orthogonal formulation"* —
`base_hasKazhdanPropertyT : HasKazhdanPropertyT.{0,0} Base`
(`LiteralBaseP13PropertyTBridge.lean:33`). **EXACT**, with a scope note: the
badged conjunct is at universe `{0,0}`, i.e. quantified over complete real
Hilbert spaces in `Type 0` only, whereas the complex conjunct is
universe-polymorphic `{0,w}`. Universe independence is available
(`HasKazhdanPropertyT.liftUniverse`, used for `P13` at
`LiteralP13HodgeCertificate.lean:254`) and is in fact invoked internally by
`hasKazhdanPropertyT_iff_textbook`, so no mathematics is missing — but the
exposed real-orthogonal statement is narrower than the printed one. **Cosmetic.**

**T3.17** *"realification and complexification identify it with the
complex-unitary formulation."* — `hasKazhdanPropertyT_iff_textbook`
(`Kazhdan/KazhdanUniverse.lean:403`). **EXACT.**

---

## 4. The generated/replay layer — the crux

The brief asks whether the generated data certifies exactly the finite data the
manuscript's argument uses, or whether it is a brute-force certification that
bypasses a manuscript step. **It does not bypass a step.** The decisive
observations:

1. **What the finite data is asked to prove is only equalities.** The interface
   is `FiniteSupportHodgeCertificate.adjoint_coordinateSum_mul_coordinateSum`
   (`Kazhdan/FiniteSupportHodgeCertificate.lean:155`), whose sole group-theoretic
   hypothesis is

   ```
   hproduct : ∀ a b, (support a)⁻¹ * support b = basis (productClass a b)
   ```

   — an *equality* in `P13`, discharged by `LiteralP13HodgeData.support_inv_mul_support`
   (line 1090) from `supportProduct_replayed`. Each of the 484 instances is a
   relator replay: a finite product of conjugates of the thirteen displayed
   relators, checked in the **free** group by `decide` and mapped down
   (`PresentedGroupRelatorReplay`, `mk_eq_mk_of_replay`). Where the two words
   are already free-group equal the proof is `rfl`; otherwise it cites a
   `reductionNN` lemma with an explicit relator-conjugate certificate
   (e.g. `reduction25`, `LiteralP13HodgeReplay.lean:1401`).

2. **No distinctness is required, so no word-problem/completeness fact leaks
   in.** This is the point where a bypass would have to live. It does not: the
   293 product classes need only be a *function* of the pair `(a,b)` with the
   displayed representative equal to `sᵃ⁻¹sᵇ`. If two distinct class indices
   happened to name the same group element, the class-wise identity
   `coefficient_identity` (`LiteralP13HodgeCertificateCore.lean:119`) still
   pushes forward to the correct group-ring identity (the coefficients simply
   add at that element), and the ℓ¹ residual bound only gets slacker by the
   triangle inequality (`l1_coordinateSum_le`). So the certificate is sound
   without any injectivity claim about the class table — which matters, because
   `thm:p13-complete` (which would supply such injectivity) is *downstream* of
   nothing here and must not be circularly assumed. It is not.

3. **The certified quantity is exactly the manuscript's.** `exactCertificate`
   (`LiteralP13HodgeCertificate.lean:189`) certifies
   `Δ₁ = (1/250)·I + Q⁺Q + R` with `∑ₖ‖R_{ik}‖_{ℓ¹} ≤ 11670886519714/10¹⁶`, i.e.
   a sum-of-squares decomposition of the degree-one Hodge matrix with integer
   Gram data and a rational residual — the printed "exact sum-of-squares
   certificate with integer matrix data". `cleanP13Certificate` then weakens the
   residual bound to `1/500` and exposes only `(1/250, 1/500)`, so downstream
   consumers see no 16-digit numerals. Gap delivered: `1/250 − 1/500 = 1/500`,
   the printed constant.

4. **`scripts/check_p13_generated.py` is a reproducibility gate, not a proof
   step.** It regenerates the four emitted sources from the pinned
   JSON/NPZ artifacts and diffs them against the checked-in modules. Its own
   header says so ("The Lean kernel is the authority for the proof"). It plays
   no role in any Lean proof; deleting it would weaken provenance, not
   soundness. Likewise `scripts/p13_build_shards.py` is pure build
   orchestration (12 shards × 3 blocks × 4 parts).

5. **All artifacts referenced actually exist**:
   `experiments/sl3-sos-radius0-certificate.npz`,
   `experiments/sl3-p13-reductions-complete.json`,
   `experiments/sl3_p13_replay_lean_generator.py`, `scripts/descent_model.py`.

Verdict on the crux: the earlier auditor's claim that "the generated replay
machinery certifies exact finite data rather than substituting a different
proof" **is correct and survives adversarial checking.** The mismatches in this
audit are elsewhere.

---

## 5. Documentation defects that would mislead an auditor

These are not soundness problems, but they are the kind of thing this audit
exists to catch, and two of them actively misdirect a reader trying to trace the
proof.

**D1. `P13DescentMaster` header is stale and self-contradicting**
(`Monsters/P13DescentMaster.lean:7-10`):

> *"Work in progress: the step construction is being assembled from the class
> rewrite lemmas; the master induction and the final assembly are complete.
> Nothing here is imported by the library root until the step lands."*

`descent_step` is complete (line 1446, all 36 cases), and the module **is**
imported by the root aggregator at `GroupApproximation.lean:65`. A reader
auditing the badge would conclude from this docstring that the completeness
theorem is not built. It is.

**D2. `P13ColumnLift` advertises a route that was abandoned, and its dead code
shadows a live name.** The header (`Monsters/P13ColumnLift.lean:9-24`) describes
a canonical column lift `rho v`, its inverse `m v`, and a cocycle
`sigma g v = rho(g·v)·g·(rho v)⁻¹`, closing with

> *"The membership of all generator cocycles in the parabolic subgroup is the
> remaining containment step and is proved in later files."*

That is **not** the route taken. Grepping the whole repository, `rho`, `m`,
`sigma`, `IsColumn` and `euclidMeas` from this module have **no consumer outside
the module**; the kernel containment is proved instead by the word descent
(`P13WordDescent` / `P13DescentCases` / `P13DescentMaster`). Only `e3`, `act`,
`act_x0…act_x5`, `act_w13`, `act_w23` and `vec3_ext` are actually used.

Worse, `P13ColumnLift.sigma` (a cocycle valued in `P13`) is shadowed by
`P13WordDescent.sigma` (the trajectory norm, `ℕ`-valued), and both namespaces
are `open`ed together in `P13DescentCore`, `P13DescentCases` and
`P13DescentMaster`. The master file has to disambiguate by hand — e.g.
`unfold P13WordDescent.sigma` at lines 29, 90, 126, 1166. This is a live
footgun and a maintenance hazard.

**What further chasing turned up (reported to the lead after first issue).** The
sentence *"proved in later files"* points at
`GroupApproximation/Monsters/P13KernelFactorization.lean`, whose own docstring
claimed the cocycle membership *"is discharged in the descent files"*. It was
not: the hypothesis

```
hσ : ∀ (i : Fin 6) (c : ℤ) (v : Fin 3 → ℤ), IsColumn v → sigma (x i c) v ∈ Hpar
```

was proved nowhere in the repository, which made
`P13KernelFactorization.toSL3_injective` a **conditional** injectivity theorem
sharing its name with the real unconditional `P13DescentMaster.toSL3_injective`
— the badge-claim-strength defect class. It was uncontaminated (zero
references; nothing opened the namespace; every live use fully qualified) but it
compiled on every build and created a name collision on the subsystem's most
important theorem, alongside the `P13ColumnLift.sigma` / `P13WordDescent.sigma`
collision.

**RESOLVED.** `Monsters/P13KernelFactorization.lean` has been deleted and the
P13 subsystem rebuilds green (`P13Completeness`, `P13DescentCore`,
`P13WordDescent`, `P13MonomialMachine` all built). D1's docstring is likewise
corrected. Remaining recommendation, unactioned: retire what is left of the dead
column-lift/cocycle section in `P13ColumnLift.lean` (everything from `IsColumn`,
line 146, to the end — now unreachable with its only consumer gone) or rename
its `sigma`.

**D3. Provenance notes that read like proof dependencies.** `P13WordDescent`'s
header (line 23-26) says the measure and case table "were validated numerically
first (`scripts/descent_model.py`)", and `P13DescentCases` (line 7-8) says the
catalog is "validated by the numerical model". Both are true statements about
*discovery*, and neither creates a proof dependency — every case is proved by
`omega` over the explicit integer coordinate action. But phrased in the header of
the file whose theorems are being audited, they invite the misreading that a
Python model is load-bearing. It is not.

---

## 6. TeX-side findings

Reported per the brief's request for anything believed wrong in the TeX or
unformalizable as printed.

**X1 (real).** The printed order of `thm:p13-complete` is not executable: the
semidirect-normal-form separation is applied, as printed, to a word that is not
in the kernel. See P13.ORDER. The fix is to move the Schreier/`w⁴` clause before
the separation clause, or to say explicitly that the separation is applied to
the recombined word `mon · (conjugated monotone part)`.

**X2 (real, minor).** Step 3's constant `3/64` in item 2 requires `κ ≤ 1`, which
is nowhere stated. Add "we may assume `κ ≤ 1`" to Step 2 or Step 3.

**X3 (minor).** ~~Step 1's *"The kernel of `Δ` is exactly the space of invariant
vectors"* asserts an equality where only one inclusion is used; harmless, but
the equality is not what gets proved.~~ **Withdrawn, 2026-08-16.** Both halves
of this are now false. The equality *is* proved
(`P13SpectralGap.t1_05_p13_ker_eq_invariants`, see the T1.05 retraction), and
both inclusions are now used: the forward one inside the Kazhdan argument, and
the converse — the one this finding called unused — by
`P13InvariantProjection.generatorLaplacian_eq_zero_of_invariant`, which is what
lets the distance estimate of T1.06 discard the invariant part of `v`. No TeX
edit is called for.

**X4 (minor).** ~~Step 3's justification for omitting `v₁` from the control set
(T3.04) is a correct but *superfluous* argument — the two-conjugate normal form
of item 2 already covers `v₁`. As printed it is a step with no role.~~
**Withdrawn, 2026-08-16.** The superfluity was an artifact of the Lean side, not
of the manuscript. The printed item 2 assumes a displacement bound on the three
*basis* translations and derives `v₁`'s from `v₁ = xv₂x⁻¹`; the repo's
`translation_eq_two_rotation_conjugates` happens to produce a stronger normal
form using only `v₃, v₂`, which is what made the printed step look idle.
`t3_02_norm_translation_displacement_le` now takes the printed hypothesis, so
the caller must discharge `v₁` and does so by the printed argument. No TeX edit
is called for.

**X5 (scholarship).** The clause *"whose elements the matrix model separates by
their semidirect normal form"* silently requires completeness of the rank-two
braid presentation. Given how much weight `thm:p13-complete` carries, a
half-sentence ("the rank-two block is faithful, by the classical
`PSL₂(ℤ) = ℤ/2 ∗ ℤ/3` ping-pong together with the central `±1`, formalized in
`Monsters/SL2Completeness`") would make the printed route self-supporting.

---

## 7. Summary table

### Reconciliation, 2026-08-16

**This table was stale against its own document.** It carried `T1.04` as
`MISSING` and `T1.05` as `MISMATCH` while the Revision note (lines 36–50) and
§3 had already retracted both to `EXACT` — the Revision note even ends *"The
recommended TeX edit is cancelled."*  The body was right and the table was not
updated with it.  That mattered outside this file: the stale row was relayed
onwards as a live finding, "the printed spectral localization of Step 1 is
absent, a Neumann/Richardson iteration with a weaker constant stands in its
place."  It is not absent.  `Monsters/P13SpectralGap.lean` is root-imported and
compiles, so `t1_04_p13_spectrum_subset` and `t1_05_p13_ker_eq_invariants` are
real.

Rows are rewritten as `OLD → NEW` rather than overwritten, so the history stays
legible.  Two kinds of change appear below.

* **Retractions by this document's own body** (`T1.04`, `T1.05`).  Nothing in
  the corpus changed; the audit corrected itself and the table lagged.
* **Rows closed by new work** (`T1.06`, `T3.01`, `T3.04`, `T3.11`), marked
  `→ EXACT pending compilation`.  That qualifier is load-bearing and is not a
  synonym for `EXACT`: the printed object now has a named Lean counterpart that
  the badged declaration actually invokes, **but the modules holding those
  counterparts have never been built.**  `Monsters/P13CircumcenterRoute.lean`,
  `Monsters/P13CircumcenterRouteStep3.lean` and `Monsters/P13SpectralGapNorm.lean`
  are imported by nothing and are absent from `GroupApproximation.lean`, so
  `lake` has never seen them; `Monsters/P13InvariantProjection.lean` is new.  A
  first probe returned `EXIT=1` for all three orphans.  Each such row reverts to
  its original mark if the build does not come back green.  Recording a verdict
  that was never checked is the error this reconciliation exists to correct, and
  it would be self-defeating to repeat it here.

One deliberate non-closure, recorded so it is not mistaken for an oversight: the
Step-1 chain that now reaches the badged declaration does **not** cite
`t1_04_p13_spectrum_subset`.  It runs through the sharp lower bound
`P13SpectralGapNorm.p13_norm_lower_bound`, derived from the certificate's
quadratic gap directly.  The localization theorem is proved and sits beside the
chain rather than in it — which is what the manuscript does too: Step 1 states
the localization, observes that it "makes `0` an isolated point of the spectrum
but does not by itself exclude it", and then switches to the lower bound.  The
Lean is mirroring the printed structure, not diverging from it, and no
dependency was manufactured to make this table read better.

| Step | Mark |
|---|---|
| P13.00 presentation (13 relators, printed order) | EXACT |
| P13.01 canonical map to elementary matrices | EXACT |
| P13.02 surjectivity = Euclidean elimination | EXACT |
| P13.03 injectivity = `K₂(3,ℤ)` in presentation form | EXACT (framing) |
| P13.04 lexicographic trajectory descent → monotone × signed-swap | EXACT on objects; UNDER-SPECIFIED interior (36-case table unprinted) |
| P13.05 squeeze at norm one | EXACT |
| P13.06 every letter fixes the base column | EXACT |
| P13.07 conjugate through the tail → parabolic | EXACT |
| P13.08 semidirect normal form separates | EXACT; UNDER-SPECIFIED (hidden `SL₂` completeness) |
| P13.09/10 six-coset Schreier, Weyl powers | EXACT |
| P13.11 `{-1,-1}=w⁴` killed by the displayed relator | EXACT |
| P13.12 kernel trivial | EXACT |
| **P13.ORDER** separation applied after, not before, the Schreier endgame | **MISMATCH (order); defect is in the TeX** |
| P13.13 isomorphism | EXACT |
| T1.01 relator display pinned | EXACT |
| T1.02 SOS certificate, gap `1/500` | EXACT |
| T1.03 quadratic gap on coboundaries | EXACT |
| **T1.04 spectrum in `{0}∪[1/500,∞)`** | **MISSING → EXACT** — retracted by this document's Revision note (lines 36–50) and §3; `P13SpectralGap.t1_04_p13_spectrum_subset`. The table, not the corpus, was wrong |
| T1.05 `ker Δ` = invariants | **MISMATCH → EXACT** — retracted in §3; `P13SpectralGap.t1_05_p13_ker_eq_invariants` proves the printed *equality*. Both inclusions are now consumed: `Δx=0 ⇒ invariant` inside the Kazhdan argument, and the converse by `P13InvariantProjection.generatorLaplacian_eq_zero_of_invariant` in T1.06 |
| **T1.06 almost-fixed ⇒ close to an invariant vector** | **MISMATCH → EXACT pending compilation** — `P13InvariantProjection.t1_06_norm_sub_fixedProjection_le`: `‖v − Pv‖ ≤ 1000·∑ᵢ‖ρ(sᵢ)v−v‖` with `P` the projection onto the invariants (= `ker Δ`), the printed constant `1000 = 2·500`. Energy half: `t1_06_energy_eq` / `t1_06_energy_le` |
| T1.07 Kazhdan pair for `P13` | EXACT; **route changed** — the badged path now runs through `P13InvariantProjection.t1_07_p13_isKazhdanPair`, which reads the pair off the projection estimate at tolerance `1/12000`, rather than through the Richardson constant of `Certificate.isKazhdanPair`. `LiteralP13HodgeCertificate.p13_hasKazhdanPropertyT` is unchanged and remains the alternate route |
| T2.01–T2.06 the six words, replay, `z`/`xy`, generation, surjectivity, quotient | EXACT |
| **T3.01 `R` maps to the linear subgroup** | **MISMATCH → EXACT pending compilation** — `P13CircumcenterRouteStep3.t3_01_rotations_hasKazhdanPropertyT` transports along the printed **surjection**, replacing `of_mulEquiv rotationEquivRotations.symm` at `LiteralBasePropertyTBridge.lean`. No retraction, no injectivity |
| T3.02 Kazhdan pair `(S,κ)` | EXACT |
| T3.03 control set `S ∪ {v₂,v₃}`, tolerance `κ/64` | EXACT (unstated `κ ≤ 1`; the TeX finding X2 stands). Lean side no longer *assumes* it: `t3_03_exists_normalized_pair` derives `κ ∈ (0,1]` from Step 2 |
| **T3.04 `v₁` needs no control because `v₁ = xv₂x⁻¹`** | **MISSING → EXACT pending compilation** — `t3_04_basis_displacement_lt`. Made load-bearing rather than decorative: T3.10's hypothesis now quantifies over all three *basis* translations, as the printed item 2 does, so the caller must discharge `v₁` and does so by the printed conjugation argument. See X4 |
| T3.05 moving projection, `‖p−ξ‖ < 1/64` | EXACT |
| T3.06 three transvection words | EXACT |
| T3.07 two-conjugate normal form | EXACT |
| T3.08 conjugate displaces `p` equally | EXACT |
| T3.09 control translations move `p` by `< 3/64` | EXACT |
| T3.10 every translation moves `p` by `≤ 1/8` | EXACT; now via `t3_02_norm_translation_displacement_le`, whose hypothesis is the printed one (a common bound on `v₁,v₂,v₃`) rather than the two the repo's normal form happens to use |
| **T3.11 Hilbert-space circumcenter** | **MISMATCH → EXACT pending compilation** — `t3_11_exists_near_translationFixedSubspace`, the centre of the smallest enclosing ball via `Circumcenter.existsUnique_center`, replacing `HilbertConvexFixedPoint.exists_near_fixedSubspace` at the single call site. The convex-hull development is untouched and remains the alternate engine |
| T3.12 orthogonal projection is nearest | EXACT |
| T3.13 normalizes and fixes ⇒ `η` fixed | EXACT |
| T3.14 generation ⇒ `B`-invariant | EXACT |
| T3.15 `‖η−ξ‖ ≤ 1/8+1/64 < 1` | EXACT |
| T3.16 real-orthogonal (T) | EXACT (universe-0 scope note) |
| T3.17 complex-unitary | EXACT |
| Generated/replay layer | **NOT a bypass** — certifies only relator-proved equalities; distinctness never needed |

**Count as first issued:** 34 EXACT, 5 MISMATCH, 2 MISSING, 2 UNDER-SPECIFIED,
3 documentation defects, 5 TeX findings.

**Count after the 2026-08-16 reconciliation:** 36 EXACT, 1 MISMATCH, 0 MISSING,
4 EXACT-pending-compilation, 2 UNDER-SPECIFIED, 3 documentation defects, 5 TeX
findings. The arithmetic: `+2 EXACT` from the two self-retractions (`T1.04`,
`T1.05`); the five MISMATCH rows were `P13.ORDER, T1.05, T1.06, T3.01, T3.11`,
of which `T1.05` became EXACT and three moved to pending, leaving `P13.ORDER`
alone; both MISSING rows (`T1.04`, `T3.04`) cleared. `34+5+2 = 41 = 36+1+0+4`.

If the four pending rows fail to compile they revert — `T1.06`, `T3.01`, `T3.11`
back to MISMATCH and `T3.04` back to MISSING, joining `P13.ORDER` — and the
count becomes 36 EXACT, 4 MISMATCH, 1 MISSING (`36+4+1 = 41`). The two
self-retractions are unaffected either way: they are corrections to this audit,
not to the corpus, and `Monsters/P13SpectralGap.lean` already compiles.

The retracted verdict was too generous in exactly one place — Step 1 of
`prop:literal-base-T`, where the ~~spectral localization and the~~
almost-fixed-vector formulation ~~are both~~ *is* replaced by a different
argument — and in three smaller places in Step 3. *(2026-08-16: the spectral
localization half of that sentence was withdrawn by the Revision note; only the
almost-fixed-vector half was ever a real gap, and it is `T1.06`.)* It was
*correct* about the completeness proof and about the replay layer, and
adversarial re-checking did not dislodge either.
