# Build notes for the 14 authored-uncompiled modules (2026-08-19)

These modules were written without a compiler, at the user's instruction, on
the understanding that someone else runs the elaboration pass.  This note
exists to make that pass cheap: it records what was already checked, what the
known-risky steps are, and what to try first when one fails.

## What was already verified

Every identifier was checked either against existing repo usage (the repo
compiles, so anything already in use is real and non-deprecated at the pin) or
against pinned Mathlib `905b95818eb32af7874a58b427f50c1711a5e96c` by
`curl`ing `raw.githubusercontent.com`.  Eight genuine defects were found and
fixed this way:

| defect | fix |
|---|---|
| `EuclideanSpace.single_apply` **deprecated** (fatal: `lakefile.toml` sets `-DwarningAsError=true`) | `PiLp.single_apply` |
| `ContinuousLinearMap.smulRight` does not exist at the pin | rebuilt `folnerIncl` via `LinearIsometry.toSpanSingleton` |
| `innerSL_apply` does not exist | `innerSL_apply_apply` |
| `lp.single_apply` returns `Pi.single i a j`, **not** an `ite` | `lp.single_apply_self` / `lp.single_apply_ne` (two proofs rewritten) |
| `FreeGroup.lift.of` does not exist | `FreeGroup.lift_apply_of` |
| `PresentedGroup.mk_eq_one` does not exist | `PresentedGroup.one_of_mem` |
| `ContinuousLinearMap.add_apply` / `smul_apply` unverified | dropped from `simp` lists (they are `@[simp]`, so `simp` still uses them) |

**Lesson for the next pass:** a wrong name inside a `simp [...]` list is a hard
error, but the lemma usually fires from the default simp set anyway.  When in
doubt, delete the name rather than guess it.

## Known-risky steps, by module

* `CStarChoiMap.isCompletelyPositive_choiMap` — the four-fold sum reordering
  goes through `sum_swap_pairs` (proved here via `Fintype.sum_prod_type`).
  If the `Finset.sum_congr` plumbing around `hleft`/`hright` misaligns, the
  mathematics is still right: both sides are
  `∑_{p,q,r,u} star(α r i u p) * α r j u q • (b_p⋆ b_q)`, only the association
  differs.
* `LanceFolnerMaps.isCompletelyPositive_compressionLM` — `hcast` uses
  `push_cast; rfl`.  If `rfl` fails, `Complex.ofReal_sum` plus
  `Complex.ofReal_pow` is the explicit route.
* `LanceFolnerMaps.norm_single_one` — `lp.norm_single (by norm_num)`; the
  hypothesis is `0 < p` at `p = 2 : ℝ≥0∞`.  There is a second, instance-driven
  form immediately after it in `lpSpace.lean` if the exponent will not
  elaborate.
* `LanceNuclearAmenable.isNuclearCStarAlgebra_of_overlap` — the `choose`
  over `hall` produces dependent families `Nn/CC/GG`; the `Finset.biUnion`
  and `Finset.single_le_sum` bookkeeping is where index mismatches will show.
* `LanceAmenableOverlap.exists_overlap_of_isAmenable` — the `field_simp` in
  `hval` is the least robust step; the identity is
  `(|A| − |∂|)/|A| − 1 = −|∂|/|A|`.
* `AdianRabinGeneral` — universe discipline: `MarkovData` is at `Type 0`
  because `PresentationCode`'s `Carrier` is.  `AdianRabinVariantTransform`
  is the model to compare against; every step there is the same modulo the
  property.
* `TorsionFreeMarkov.c2gen_sq` — `ring_nf; rfl` on `Multiplicative (ZMod 2)`;
  `decide` is the fallback.

## Nothing here contains `sorry`

If a proof cannot be repaired, the honest move is to delete the declaration,
not to weaken it to a hypothesis — several of these modules exist precisely to
*remove* typed hypotheses from the corpus, and a `sorry` or a re-introduced
binder would invert their purpose.

## Do not retire quarantine rows before this is green

`metadata/LITERATURE_QUARANTINE.md` is deliberately untouched.  The doctrine is
retire-in-the-same-commit-as-the-proof, and none of this has passed the kernel.
The rows these modules would retire, once green, are Lance, Adian--Rabin, and
(by elimination rather than proof) Tu; the Kun--Thom row should be reworded to
name Shulman and Kun--Thom as two separate citations.
