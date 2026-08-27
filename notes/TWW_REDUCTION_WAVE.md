# Tikuisis--White--Winter: the reduction wave (local form, transcription
# validation, and the amenable-trace split)

**Authored 2026-08-19.  UNCOMPILED.**  Three modules, written without a build
because the instruction was *"do NOT run builds or compile or run any code,
just edit / add"*.  Nothing here has been elaborated by Lean.

**Companion note:** `notes/TWW_UNCONDITIONAL_WAVE.md` is a *different* lane
working the same instruction in this checkout (compression models, the
`0`-or-`≥1` dichotomy, locally finite groups, Lance, the ucp bound).  The two
are complementary and share no declaration; that note is theirs, this one is
mine, and both lanes are uncompiled.

## The honest answer, first

**The theorem is not provable in this repository, and these modules do not
prove it.**  No declaration added here concludes it or inhabits an input that
states it.

The published proof consumes, at minimum: the Kirchberg--Rørdam structure
theory of the corona `∏ M_k / ⊕ M_k`; completely positive contractive
**order-zero** maps and the cone `C_0((0,1]) ⊗ A` picture of them;
Voiculescu's theorem; `KK`-theory, the Rosenberg--Schochet universal
coefficient theorem, and the **Dadarlat--Eilers stable uniqueness theorem**,
which is where the UCT hypothesis is actually consumed; and the tracial
machinery of Ozawa--Rørdam--Sato.  Of that list, `KK`-theory, the UCT,
order-zero maps and the Cuntz semigroup have **no definition in mathlib and
none here**.  The instruction's own parenthesis --- *irreducible, there is no
elementary route* --- is correct.

Three ways to fake it were available and all three were declined: a `sorry`; a
definition of "quasidiagonal" weak enough to make the statement provable
([[badge-claim-strength]] names that defect class); and a circular route
through an input that is the theorem under another name.

## What was done instead

Drive the conditional surface down to the irreducible core and prove
everything around it --- the house style of
`Analysis/TikuisisWhiteWinter.lean` and
`Sofic/FournierFacioUniversalGroup.lean`: take the citation apart, name each
piece, prove the connective tissue.

### `Analysis/QuasidiagonalTraceLocal.lean` --- the local form

`QuasidiagonalTraceModel` is a *sequence* of models.  **That is not the form
Tikuisis--White--Winter prove.**  The paper proves the finite-set/`ε` form: for
every finite `F ⊆ A` and `ε > 0`, **one** ucp `φ : A → M_k` with both defects
`≤ ε` on `F`.  This module supplies that form and proves both passages.

* `isLocallyQuasidiagonalTrace_of_isQuasidiagonalTrace` --- free, via
  `eventually_finset`.
* `lipschitz_of_isLocallyQuasidiagonalTrace` --- **a locally quasidiagonal
  trace is `1`-Lipschitz.**  The find of the wave: the obvious formulation of
  the diagonal argument carries continuity of `τ` as a hypothesis, and it does
  not have to, because the models control `τ` at *every* point of `A` and not
  only on a dense subset.  At `{x, y}` the trace clause pins `τ x` and `τ y`
  to within `ε` of two matrix traces whose difference is at most `‖x − y‖`.
  So no state-theoretic input (`‖τ‖ = τ(1) = 1`, which this repository does
  not prove) enters anywhere.
* `isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace` --- the diagonal
  argument: exhaust a separable `A` by a dense sequence, take the model for
  `{u 0, …, u n}` at tolerance `1/(n+1)`, move an arbitrary pair to a nearby
  dense pair with `norm_mul_defect_le`.  **Separability is its only
  hypothesis.**  The contraction bound it also uses is
  `Quasidiagonal.ucpContractive` (`Analysis/UCPContractiveMatrix.lean`, landed
  `ab6c1459`, root-imported), so the module carries no binder at all.

* `isLocallyQuasidiagonalTrace_of_dense` --- **it is enough to test the local
  form on a dense subset.**  This is where every real proof of a
  quasidiagonality statement starts: one does not check the defects at
  arbitrary elements, but at a dense `⋆`-subalgebra --- for a group
  C⋆-algebra, at finitely many group elements --- and lets the estimates
  propagate.  Same two estimates as the diagonal argument, with explicit
  constants (`C = ∑_{x∈F} ‖x‖`, `δ ≤ 1` with `(4C+2)δ ≤ ε/2`).

  Note the asymmetry with the item above, which is real and is documented in
  the docstring: this theorem **does** take `1`-Lipschitz continuity of `τ` as
  a hypothesis, because a hypothesis controlling `τ` only on `D` says nothing
  about `τ` off `D`.

Net effect: the statement the repository assumes got strictly weaker.

### `Analysis/QuasidiagonalTraceProperties.lean` --- the transcription, validated

`QuasidiagonalTraceModel` takes `τ : A → ℂ` as a bare function; **no clause
says `τ` is linear, tracial, positive or unital.**  If the transcription were
wrong that is exactly where it would show.  Proved here, with no input at all:

* `τ` is `ℂ`-linear; `τ(xy) = τ(yx)`; `0 ≤ τ(x⋆x)`; and `τ(1) = 1`
  **provided the models are nonempty**;
* `QuasidiagonalTraceModel.toTracialState` --- the four together.

The nonemptiness caveat is a theorem, not a hedge: `isQuasidiagonalTrace_zero`
shows the **zero functional is a quasidiagonal trace**, witnessed by empty
models, because `M_0(ℂ)` is the zero ring.  `ShulmanTrace.MFTraceModel` has the
same feature (`exists_shift`); in both cases the omission is faithful to the
source, which supplies nonempty models.

Also here: `QuasidiagonalTraceModel.comp` (pullback along a unital
`⋆`-homomorphism) and a **positive control**,
`isQuasidiagonalTrace_complex` --- the identity trace on `ℂ` is quasidiagonal,
every defect identically zero.  `ℂ` is separable, nuclear and UCT with a
faithful trace, so that is a genuine instance of the theorem, the smallest
one.  It matters for a reason unrelated to TWW:
`Sofic/TikuisisWhiteWinterSites.lean` proves a particular trace is **not**
quasidiagonal, and a negative statement about an unsatisfiable predicate is
true and empty.  The other lane's locally finite theorem is a far better
inhabitant; this one is the cheap backstop that does not depend on that lane
compiling.

`isQuasidiagonalTrace_of_character` extends it off the finite-dimensional
case for free: composing the scalar models with a unital `⋆`-homomorphism
`π : A → ℂ` shows **every character on any unital C⋆-algebra is a
quasidiagonal trace** --- for `C(X)`, one for each point of `X`.  That is not
a special case of the theorem in any useful sense (a character is
quasidiagonal for reasons unrelated to nuclearity or the UCT), but it puts an
inhabitant of `IsQuasidiagonalTrace` at infinite-dimensional algebras using
only what this lane proves.

### `Analysis/TikuisisWhiteWinterCore.lean` --- the citation, taken apart

`TikuisisWhiteWinterInput` bundles two different people's theorems and a
diagonal argument.  Split:

| | statement | owner |
|---|---|---|
| 1 | amenable trace = ucp models approximately multiplicative in the **`2`-norm** | `AmenableTraceModel` --- definition |
| 2 | on a nuclear algebra every trace is amenable | `NuclearAmenableTraceInput` --- Connes/Haagerup/Choi--Effros; **input** |
| 3 | faithful **amenable** trace on separable nuclear UCT ⟹ **locally** quasidiagonal | `TikuisisWhiteWinterCoreInput` --- TWW; **input** |
| 4 | locally quasidiagonal + separable ⟹ quasidiagonal | **proved**, previous module |

`isQuasidiagonalTrace_of_core` assembles 2 + 3 + 4, and
`tikuisisWhiteWinterStatement_of_core` states that assembly at the level of
the named proposition below.  `AmenableTraceModel` is
`QuasidiagonalTraceModel` with exactly one clause weakened from `‖·‖` to
`‖·‖₂`, which makes the shape of the theorem visible: **TWW does not produce
models where there were none, it upgrades the norm in which existing models
are approximately multiplicative.**  The converse,
`isAmenableTrace_of_isQuasidiagonalTrace`, is proved unconditionally from
`‖x‖₂ ≤ ‖x‖`, so under the four hypotheses the two notions coincide and the
citation is exactly the hard direction of an equivalence whose easy direction
is now in the tree.  `isOperatorMF_of_isAmenable_of_core` re-derives the
printed `INT.11` over the finer inputs.

### The theorem as a proposition one can point at

Until this wave the Annals statement existed here only as a **field** of
`TikuisisWhiteWinterInput` --- nameable only by assuming the structure that
carries it.  `TikuisisWhiteWinterStatement (UCT) : Prop` writes it out
standing alone, and `tikuisisWhiteWinterStatement_iff_input` proves the two
carry the same content, so the change of shape smuggles nothing.

**It is a definition, not a theorem, and it has no proof anywhere in this
tree.**  What is formalized is the *statement*.  The *proof* is
Tikuisis--White--Winter's and is not reproducible here.  The value of writing
it down is that `tikuisisWhiteWinterStatement_of_core` can then say exactly
which weaker assumptions imply it, and that the ledger and the quarantine gate
have an object to name.

## Accounting

Before: one input, `TikuisisWhiteWinterInput`, asserting the sequence form at
every faithful trace on a separable nuclear UCT algebra, plus
`UCPContractive`.

After: two inputs --- `NuclearAmenableTraceInput` (Connes--Haagerup) and
`TikuisisWhiteWinterCoreInput` (the Annals theorem, in its own form and at its
own hypothesis).  Everything else that used to sit inside the bundle is
proved: local ⟹ sequence, continuity of `τ`, and
positivity/traciality/linearity/unitality of `τ`.  `UCPContractive` is
inhabited by the other lane, so [[literature-quarantine-gate]]'s entry for it
--- the only roster line that note called retirable outright --- can go.

## One edit to an existing file

`Analysis/QuasidiagonalTrace.lean`: `diracVec` and `form_diracVec` were
`private` and are now public, because the positivity proof reads the
complete-positivity clause at a single `δ`-vector.  No statement changed.

## First-compile suspicion list, in order

1. `isCompletelyPositiveOnMatrices_scalarModelMap` (Properties) --- the
   five-fold sum rearrangement.  `sum_comm₃`, `Finset.sum_ite_eq`,
   `Finset.sum_mul_sum`, `Complex.mul_conj`, `Complex.ofReal_sum` are used
   with guessed argument orders.  The mathematics is `∑_p |∑_j z_j w_j(p)|²`;
   only the plumbing is at risk.
2. `scalarModelMap_entry` --- `rw [scalarModelMap_apply, Matrix.diagonal_apply]`.
   If `Matrix.diagonal_apply` is stated through `Matrix.of`, use
   `diagonal_apply_eq` / `_ne` with `by_cases`.
3. `normTrace_nonneg_of_isCompletelyPositive` (Properties) --- mirrors
   `ShulmanTrace.normTrace_star_mul_self_nonneg`; the risky step is
   `simp only [Matrix.trace, Matrix.diag]` before `Finset.sum_nonneg`.
4. `isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace` (Local) --- the final
   `linarith` over monomials `‖a‖·δ`, `‖b‖·δ`, `δ`; if it fails, split
   `hprod`/`hlast` into single-product `have`s.
   `TopologicalSpace.exists_dense_seq` and `DenseRange.exists_dist_lt` are
   name guesses.
5. `map_mul_comm_of_isQuasidiagonalTrace` (Properties) --- five-term telescope
   closed by `linarith` over three `norm_sub_le`/`norm_add_le` facts; if the
   association of the `+`s does not match, rewrite as an explicit `calc`.
6. `QuasidiagonalTraceModel.compStarAlgHom` --- `π.toAlgHom.toLinearMap` and
   three `by simp` obligations.  If the coercion tower fights back, use
   `QuasidiagonalTraceModel.comp` directly; it takes the three algebraic facts
   as hypotheses precisely so this is a fallback and not a blocker.
7. `exists_small_scale` (Local) --- `field_simp` on `K * (ε / K) = ε`.
8. `isQuasidiagonalTrace_zero` --- `ext p q; exact p.elim` on
   `Matrix Empty Empty ℂ`, and the two `simp`s.

9. `isLocallyQuasidiagonalTrace_of_dense` (Local) --- the newest and longest
   proof: `Dense.exists_dist_lt`, `Finset.single_le_sum` with an explicit
   `(f := ...)`, `Finset.coe_image`, and a `refine ... ?_ ... · ... · ...`
   whose side goal (`↑(F.image d) ⊆ D`) is discharged last.

None is a mathematical risk; each is a name or tactic-shape risk of the kind
[[authoring-lean-without-a-compiler]] catalogues.

## Roster obligation, once these compile

`TikuisisWhiteWinterStatement`, `TikuisisWhiteWinterCoreInput` and
`NuclearAmenableTraceInput` are corpus-defined `Prop`s whose content is a
theorem this repository does not prove, so all three belong on
`literaturePackages` in `scripts/Audit.lean` beside the existing
`TikuisisWhiteWinterInput` --- see [[literature-quarantine-gate]] for why a
*conclusion* structure needs its own line even when it looks derived.  The
edit is deliberately **not** made in this wave: `scripts/Audit.lean` is shared,
and the three names exist in no compiled tree yet, so adding them now would
red the audit for every other lane.  It is the first thing to do after the
first green build.

In the other direction, `Quasidiagonal.UCPContractive` can come **off** the
roster: `Analysis/UCPContractiveMatrix.ucpContractive` inhabits it.

## Before anything here is graded

All three modules are **uncompiled**, and a peer session has already wired
them into `GroupApproximation.lean` (lines 1291--1293) alongside its own
untracked modules.  Nothing in either lane may be quoted as proved, or cited
from the manuscript, or graded in the proof ledger, until a green
`Build and audit`.  Ingredient 3 stays a citation regardless.
