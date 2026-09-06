# Lane `cc-lix-odd` — mapping torus (Step B), the section and its zero (Step C), Lemma 2

Owns `GroupApproximation/CharClass/MappingTorus*.lean`,
`GroupApproximation/CharClass/LIXSection*.lean`,
`GroupApproximation/CharClass/LemmaTwo*.lean`, plus (per the lead's continuation
briefing) the two never-verified section modules
`GroupApproximation/AlgTop/{ManuscriptSectionZeroCount,CPTautologicalSection}.lean`
and their transitive dependency `AlgTop/ComplexProjectiveBasic.lean`, now repaired
in place. Namespace `GroupApproximation.CharClass` (`GroupApproximation.AlgTop` for
the two AlgTop files).

## 1. GREEN

*(job counts appear here only after a probe prints `Build completed successfully (N jobs)`
with a `Built …` line for the module.)*

| module | job count | content |
|---|---|---|
| `CharClass/MappingTorusProjection.lean` | 8662 | `IsCornerUnitary`, `cornerExtend`, `mtSym`/`mtProj` (clutched projection), `mtTrans`, `IsCircleChart`, `sphereOne`/`northPole`/`southPole`, `mappingTorus` = `W_g`, `mappingTorus_isStarProjection`, `mappingTorus_continuous`, `mappingTorus_north` (`V ⊕ 0` on the nose), `mappingTorus_south`, `trace_mappingTorus` |
| `CharClass/MappingTorusSection.lean` | 8662 | `mappingTorus_eq` (block normal form), `IsMTSectionData`, `mtSection`, `mtSection_continuous`, `mtSection_mem`, `mtSection_eq_zero_iff`, `mtSection_eq_zero_iff_of_north_ne_zero` |
| `CharClass/LIXSectionPath.lean` | 8662 | `unitVectors_seam_eq_zero_iff`, `manuscriptPath`/`southParam`, `isMTSectionData_manuscript` (the manuscript's pair descends, seam = `g e = s`), `manuscriptPath_eq_zero_iff_split` |
| `AlgTop/ManuscriptSectionZeroCount.lean` | 8662 | `productDualTautSection_eq_zero_iff`, `manuscriptSection_eq_zero_iff`/`_zero_unique`/`_zero_exists` — repaired: two `basePoint_entry_of_*_ne_zero` proofs and an `hne` cast lemma in the sibling `CPTautologicalSection.lean` |
| `AlgTop/CPTautologicalSection.lean` | 8662 | `dualTautSection_eq_zero_iff`, `tautChartHomotopy_eq_zero_iff` (mod-2 transversality) — repaired |
| `AlgTop/ComplexProjectiveBasic.lean` | 8662 | one unused-simp-arg fix (`baseVec_apply_of_ne`); this file blocked `cc-thom`/`cc-projective` too (see their reports) and is now green |
| `CharClass/LemmaTwoZero.lean` | 8658 | **Step C, transported.** `blockNorth`/`blockSouth` (the manuscript's pair in block-split form), `sumElim_eq_zero_iff'`/`continuous_sumElim_left'`/`continuous_sumElim_right'` (mixed-type `ι ⊕ κ` analogues of `MappingTorusSection`'s same-type `n ⊕ n` lemmas), `isMTSectionData_blockSplit`, `height_eq_neg_one_of_horiz_eq_zero`, **`mtSection_manuscript_eq_zero_iff`**: the transported section vanishes iff the circle point is the south pole and `b = -a`, `c = 0` at the base point |

Six commits: `256bca90b`, `c9de38ba0`, `addd8ebc6` (see git log for the intermediate
fix commits folded into the first of these).

## 2. AUTHORED, UNVERIFIED

* `CharClass/LemmaTwoUnitary.lean` — `cornerExtend_mulVec_eq` is **verified green
  standalone** (checked in isolation against `LemmaTwoZero`'s dependency tree,
  8659 jobs, then folded back in). `exists_isCornerUnitary_of_stepA` wires
  `cs-clutching`'s `STW59.exists_continuous_corner_unitary_apply_eq`
  (`Analysis/LIXObstructionComplementUnitary.lean`) into `cornerExtend`/
  `isCornerUnitary_cornerExtend`, discharging `mappingTorus`'s `IsCornerUnitary`
  hypothesis directly from a continuous Murray–von Neumann equivalence of
  complements. **Cannot be probed**: its only non-Mathlib import,
  `LIXObstructionComplementUnitary.lean`, is itself red at the pin (see TRAPS).
  Not a `sorry`/`axiom`; it is a real proof blocked on a real dependency.

## 3. NEEDS

### From `cs-clutching` — Step A (UPDATE: mostly resolved, one file still red)

**Resolved, exactly as asked.** `Analysis/LIXObstructionComplementUnitary.lean`
now has `STW59.exists_continuous_corner_unitary_apply_eq`, matching my prior
request almost verbatim (its own docstring says so): a continuous field `V`, unit
vector fields `e, s` fixed by `V`, and a continuous field of partial isometries
`w₁` implementing the equivalence of the complements (via the `colAt` column
embedding) ⇒ a continuous corner unitary `g` with `g *ᵥ e = s`. `CharClass/
LemmaTwoUnitary.lean`'s `exists_isCornerUnitary_of_stepA` consumes it directly.

**Blocking**: `LIXObstructionComplementUnitary.lean` is currently **red** —
`colAt_apply`'s proof (`Matrix.vecMulVec_apply v (Pi.single k0 1) i j`) fails with
a type mismatch at line 295, and every downstream use of `colAt_apply` then fails
with "unknown identifier" (11 occurrences), cascading into unsolved goals in
`colAt_conjTranspose`, `colAt_mul_colAt_conjTranspose`,
`colAt_conjTranspose_mul_colAt_of_normSq_one`, `colAt_pi_of_normSq_one`,
`vecMulVec_mul_of_selfAdjoint_of_mulVec_eq`, `colAt_injective`, and finally two
`rewrite` failures inside `exists_continuous_corner_unitary_apply_eq` itself
(lines 417, 438 as of this report — the exact line numbers moved between my two
probes today, so the file is being actively edited; last probe still red).
**This is `cs-clutching`'s file, not touched.** Once it is green, probe
`CharClass.LemmaTwoUnitary` — I expect it to go green on the first try, since the
interface match was checked by eye against the current (red) source.

### From `cc-thom` / the toolkit lanes — Step C's odd-side nonvanishing

`cc-thom`'s `topChernClass_ne_zero` (`CharClass/EulerLocalNonvanishing.lean`,
green, 2911 jobs) needs a `CohomologyToolkit` instance plus relative-cohomology
exactness/excision/homeomorphism-invariance/a one-dimensional local generator —
still awaiting, by cc-thom's own report: (A1)/(A2) Mayer–Vietoris and Künneth
vanishing from `cc-cohom-api`; (B3)/(B4)/(B6) excision, pair-homeomorphism
invariance, and the local generator from `cc-relative`; (C1)–(C4) the projective-
bundle pair and trivializing charts from `cc-bundle`; (D1)/(D2)/(D3)/(D5) Leray–
Hirsch, `CP^d` cohomology, and the puncture-homotopy-equivalence from
`cc-projective`. None of this is close enough to assemble yet. My own
contribution to Step C — the *combinatorial* content ("exactly one zero, at an
explicit point, with an explicit local chart") — is fully delivered in
`LemmaTwoZero.lean` and `AlgTop/{ManuscriptSectionZeroCount,CPTautologicalSection}
.lean`; what remains is purely the cohomological machinery that turns "one zero,
local homeomorphism" into "class nonzero," which is not this lane's vocabulary
to build (it is items 1–5 of the program note's §1.4, owned by five other lanes).

### From `cc-wu` — Step D's even-side vanishing

No `cc-wu` lane report file exists yet (`notes/lix-lane-reports/` has none named
`cc-wu.md`). `CharClass/{ParityEven,ParityEventSlice,WuDiagonal,WuSymmetric}.lean`
exist and are being actively edited (appeared in nearly every probe's "changed"
sync list today) but I have not read them in detail; I need the final
`ParityData`-consuming conclusion `γ_r(W) = 0` for a bundle restricting to `V` on
the slice, in element form, to state the final assembly.

### Assembly, once the above land

The final `LemmaTwoZero.lean`/`LemmaTwoUnitary.lean` pair plus `cc-thom`'s odd
nonvanishing and `cc-wu`'s even vanishing assemble by direct contradiction:
Step A (`LemmaTwoUnitary`) turns an assumed `MurrayVonNeumannEquiv` of the
complements into a corner unitary; Step B (`MappingTorusProjection`) turns it
into `W_g`; Step C (`LemmaTwoZero` + the toolkit) gives `γ_r(W_g) ≠ 0`; Step D
(`cc-wu`, applied to `W_g`, which restricts to `V` on the slice by
`mappingTorus_north`) gives `γ_r(W_g) = 0`. I have not written this final
contradiction lemma yet because two of its four inputs (odd nonvanishing,
even vanishing) do not exist in usable form yet; writing the shell now against
unstable, still-changing peer signatures would need to be rewritten anyway. I
will write it as soon as either lands in a form I can cite by name.

## 4. TRAPS

* **The Whitehead path does not descend**; clutching over the two-point equator
  does. (Recorded in full in the previous version of this report; still the
  right call, and `MappingTorusProjection.lean`'s green build confirms it.)
* **`MappingTorusSection.lean`'s `Sum.elim`/continuity lemmas (`sumElim_eq_zero_iff`,
  `continuous_sumElim_left`/`_right`) are specialized to the *doubled* index
  `n ⊕ n`** that the clutching construction itself produces (north/south copies of
  the *same* ambient type `n`). They do **not** apply to the *different*-typed
  split `ι ⊕ κ` (trivial block `⊕` transverse block) that `V = 1³ ⊕ H` actually
  needs for Lemma 2 — instantiating them there is a silent type-domain mismatch
  that surfaces as "Type mismatch… `Continuous.{max u_3 ?u.38, u_1}`" with no
  obvious pointer to the real cause. `LemmaTwoZero.lean` restates mixed-type
  versions (`sumElim_eq_zero_iff'`, `continuous_sumElim_left'`/`_right'`) rather
  than trying to force the same-type ones; do this again for any future ambient
  splitting into differently-typed blocks.
* **A bare `0` on one side of an `=` inside a hypothesis needs its own type
  ascription even when the other side already pins the ambient ring.**
  `Sum.elim (0 : ι → ℂ) (c m) = Sum.elim 0 (c m)` (RHS unannotated) fails with
  "numerals are data in Lean, but the expected type is universe polymorphic and
  may be a proposition" — annotate both sides.
* **`omit [...] in` must precede the docstring, not follow it** (already in
  memory as `omit-and-rw-placement-traps.md`; re-confirmed twice today —
  `/-- doc -/\nomit [...] in\ntheorem …` is a parse error, "unexpected token
  'omit'; expected 'lemma'"; the correct order is `omit [...] in\n/-- doc -/\ntheorem …`).
* **Do not omit a typeclass instance just because a *later*, simpler-looking
  lemma in the same file does not need it.** `blockSouth_eq_zero_iff`'s
  *statement* needs `Fintype ι`/`Fintype κ`/`DecidableEq ι`/`DecidableEq κ`
  (transitively, because `manuscriptPath`'s ambient index is `ι ⊕ κ`), even
  though the sibling `blockNorth_eq_zero_iff` (built from my own
  `sumElim_eq_zero_iff'`, which needs no Fintype at all) does not. Trust the
  linter's *specific* list per theorem, not a pattern copied from a neighbour.
* `Complex.norm_real : ‖(↑r : ℂ)‖ = ‖r‖` lands you in the **real** norm, not
  `|r|` directly — `Real.norm_eq_abs` is a second, separate rewrite that must be
  in the same `simp only` list as `sq_abs`, or `sq_abs` silently reports
  "unused" and the goal is left with `‖1 - τ‖ ^ 2` instead of `(1 - τ) ^ 2`.
* **A term-mode combinator chain (`(h1.add h2).add h3`) can fail to unify
  against a goal that needs the SAME arithmetic expression unfolded from a
  different `def`** (here, `manuscriptPath_apply`), even though the two sides
  are genuinely defeq — the safe pattern is `simp only [manuscriptPath_apply]`
  (or whatever the unfolding lemma is) **first**, then `refine Continuous.add
  (Continuous.add ?_ ?_) ?_` goal-directed, never a bottom-up term.
  `southParam`'s own continuity needed `unfold southParam` before
  `Continuous.div_const`, same root cause.
* `Complex.ofReal_ne_zero : (z : ℂ) ≠ 0 ↔ z ≠ 0` exists at this pin
  (`Mathlib/Data/Complex/Basic.lean:140`); prefer it over `simpa using ne_of_gt …`
  for casting a real strict-positivity fact to a complex nonvanishing fact — the
  `simpa` route can leave a real/complex type mismatch depending on how eagerly
  the default simp set distributes the outer cast through `+`/`-`/`*` inside the
  hypothesis versus the goal.
* `AlgTop/ComplexProjectiveBasic.lean`'s `basePoint_entry_of_row_ne_zero`/
  `_of_col_ne_zero` were provable in one `rw` chain via
  `basePoint_entry, baseVec_apply_of_ne, {zero_mul, star_zero, mul_zero}` —
  the original `simp [Pi.single_apply, ha]` failed because `baseVec` is a plain
  `def` (`Pi.single 0 1`), not reducible/simp-unfoldable, so `Pi.single_apply`
  never got the chance to fire on it.
* **`LIXObstructionComplementUnitary.lean` (`cs-clutching`) is genuinely red at
  the pin right now**, not merely "never probed" as the program note said this
  morning — it has been under heavy concurrent edit all day (present in nearly
  every one of my probes' "N module(s) changed since last sync" lists) and the
  break has moved between probes (line 295 → later, line 417 → 438). Do not
  build against it without re-probing first; it only imports `Mathlib` and
  `Analysis/LIXClutching.lean`, so it is otherwise a safe, self-contained import
  once fixed.
