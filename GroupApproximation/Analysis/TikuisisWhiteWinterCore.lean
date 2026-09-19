import GroupApproximation.Analysis.QuasidiagonalTraceLocal
import GroupApproximation.Analysis.QuasidiagonalTraceProperties
import GroupApproximation.Analysis.TikuisisWhiteWinter

/-!
# Taking the Tikuisis--White--Winter citation apart

`Analysis.TikuisisWhiteWinter` types the theorem as one opaque input,
`TikuisisWhiteWinterInput`: *every faithful trace on a separable nuclear
C⋆-algebra satisfying the UCT is quasidiagonal.*  That is the right
transcription of the printed sentence, and it is the wrong granularity for
asking what the theorem costs, because the published statement is not a single
implication.  It is

> Tikuisis, White, Winter, *Quasidiagonality of nuclear C⋆-algebras*,
> Ann. of Math. (2) **185** (2017), 229--284, Theorem A: **every faithful
> amenable trace** on a separable nuclear C⋆-algebra satisfying the UCT is
> quasidiagonal,

together with the standing fact that on a nuclear algebra *every* trace is
amenable, which is a different theorem by different people.  This file splits
the input along that seam and proves everything between the pieces.

## The four ingredients, and who owns each

| | statement | owner |
|---|---|---|
| 1 | a trace is **amenable** when it has ucp matrix models that are approximately multiplicative in the **`2`-norm** | `AmenableTraceModel` --- a definition |
| 2 | on a nuclear C⋆-algebra every trace is amenable | `NuclearAmenableTraceInput` --- Connes, Haagerup, Choi--Effros; **input** |
| 3 | a faithful amenable trace on a separable nuclear UCT algebra is **locally** quasidiagonal | `TikuisisWhiteWinterCoreInput` --- TWW; **input** |
| 4 | locally quasidiagonal + separable ⟹ quasidiagonal | `Quasidiagonal.isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace` --- **proved** |

and the assembly `isQuasidiagonalTrace_of_core` is proved from 2, 3, 4.

Two things are gained by the split, and they are the point of the file.

**The assumed statement got weaker.**  Ingredient 3 asks only for the *local*
form --- one ucp map per finite set and tolerance --- which is what the paper
proves, and it asks it only of *amenable* traces, which is what the paper
hypothesizes.  `TikuisisWhiteWinterInput` asked for the sequence form at every
faithful trace, i.e. for the paper's theorem plus a diagonal argument plus
ingredient 2.  Both extras are now theorems or separate citations.

**The converse is unconditional.**  `isAmenableTrace_of_isQuasidiagonalTrace`
proves that a quasidiagonal trace is amenable --- the `2`-norm defect is
dominated by the operator-norm defect, `‖x‖₂ ≤ ‖x‖`.  So under the hypotheses
of ingredient 3 the two notions coincide, and Tikuisis--White--Winter is
exactly the hard direction of an equivalence whose easy direction is proved
here.

## What is irreducible, said plainly

Nothing in this file, and nothing anywhere in this repository, proves
ingredient 3, and no elementary route to it exists.  The published proof runs
through: the Kirchberg--Rørdam structure theory of the corona
`∏ M_k / ⊕ M_k`; completely positive contractive order-zero maps and their
cone picture; Voiculescu's theorem; `KK`-theory, the Rosenberg--Schochet
universal coefficient theorem, and the Dadarlat--Eilers stable uniqueness
result, which is where the UCT hypothesis is consumed; and the tracial
machinery of Ozawa--Rørdam--Sato.  Of that list, `KK`-theory, the UCT and
order-zero maps have no definition in mathlib or here --- which is also why
the `UCT` predicate enters every statement below as an uninterpreted
parameter.  The honest formalization is the reduction, not the theorem.

What *is* proved unconditionally, and is a genuine instance of ingredient 3,
is the scalar case: `Quasidiagonal.isQuasidiagonalTrace_complex`
(`Analysis.QuasidiagonalTraceProperties`) exhibits the models for the identity
trace on `ℂ`, which is separable, nuclear and UCT with a faithful trace.

**No inhabitant of either input is constructed here, and no declaration below
concludes an input structure from premise-free hypotheses** --- the
conclusions are pointwise, with head `IsQuasidiagonalTrace` or
`IsOperatorMF`, for the reason `Analysis.AmenableMFInput` and
`Analysis.TikuisisWhiteWinter` record: a premise-free producer would enter the
discharge fixpoint of `scripts/check_non_mf_unconditional.py` and the input
would stop being reported open.
-/

namespace GroupApproximation

universe u

namespace Quasidiagonal

open Filter Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section

variable {A : Type u} [CStarAlgebra A]

/-! ## Ingredient 1: amenable traces -/

/-- **An amenable trace**, in the sense the quasidiagonality literature uses
(Connes' condition; Brown--Ozawa, *C⋆-algebras and Finite-Dimensional
Approximations*, Chapter 6): unital completely positive matrix models whose
multiplicative defect vanishes in the **normalized Hilbert--Schmidt norm**,
with normalized traces converging to `τ`.

Field for field this is `QuasidiagonalTraceModel` with one clause weakened:
`‖φₙ(ab) − φₙ(a)φₙ(b)‖₂ → 0` instead of `‖φₙ(ab) − φₙ(a)φₙ(b)‖ → 0`.  The
weakening is the entire content of the Tikuisis--White--Winter theorem --- it
is the gap between a `⋆`-homomorphism into a *tracial* ultrapower, which
amenability of the trace gives for free, and one into the *norm* corona, which
is what quasidiagonality asks. -/
structure AmenableTraceModel (τ : A → ℂ) where
  /-- The finite matrix sizes `kₙ`. -/
  space : ℕ → FiniteModel
  /-- The maps `φₙ : A → M_{kₙ}`, genuinely `ℂ`-linear. -/
  map : ∀ n : ℕ, A →ₗ[ℂ] Matrix (space n) (space n) ℂ
  /-- Each `φₙ` is unital. -/
  map_one : ∀ n : ℕ, map n 1 = 1
  /-- Each `φₙ` is completely positive. -/
  completelyPositive : ∀ n : ℕ, IsCompletelyPositiveOnMatrices (space n) ⇑(map n)
  /-- Asymptotic multiplicativity in the normalized Hilbert--Schmidt norm. -/
  tendsto_mul_hs : ∀ a b : A,
    Tendsto (fun n ↦ hsNorm (space n) (map n (a * b) - map n a * map n b))
      atTop (nhds 0)
  /-- The normalized traces of the models converge to `τ`. -/
  tendsto_trace : ∀ a : A,
    Tendsto (fun n ↦ ‖τ a - normTrace (space n) (map n a)‖) atTop (nhds 0)

/-- `τ` is an amenable trace: models in the sense of `AmenableTraceModel`
exist.  This is the hypothesis of Tikuisis--White--Winter's Theorem A. -/
def IsAmenableTrace (τ : A → ℂ) : Prop :=
  Nonempty (AmenableTraceModel τ)

/-! ## The easy half of the equivalence, proved -/

/-- **A quasidiagonal trace is an amenable trace.**  Only the multiplicative
clause changes, and it weakens through the first printed inequality
`‖x‖₂ ≤ ‖x‖` (`ShulmanTrace.tendsto_hsNorm_of_tendsto_opNorm`).  The four
other clauses are transcribed unchanged.

So Tikuisis--White--Winter is the converse of a triviality, under its four
hypotheses.  Recording the triviality is what makes the shape of the citation
visible: the theorem does not produce models where there were none, it
upgrades the norm in which existing models are approximately multiplicative. -/
def QuasidiagonalTraceModel.toAmenableTraceModel {τ : A → ℂ}
    (M : QuasidiagonalTraceModel τ) : AmenableTraceModel τ where
  space := M.space
  map := M.map
  map_one := M.map_one
  completelyPositive := M.completelyPositive
  tendsto_mul_hs a b :=
    ShulmanTrace.tendsto_hsNorm_of_tendsto_opNorm (Y := M.space)
      (X := fun n ↦ M.map n (a * b) - M.map n a * M.map n b)
      (M.tendsto_mul a b)
  tendsto_trace := M.tendsto_trace

/-- The proposition-level form. -/
theorem isAmenableTrace_of_isQuasidiagonalTrace {τ : A → ℂ}
    (h : IsQuasidiagonalTrace τ) : IsAmenableTrace τ := by
  obtain ⟨M⟩ := h
  exact ⟨M.toAmenableTraceModel⟩

/-- **The scalar case of the equivalence**, both directions unconditional: the
identity trace on `ℂ` is quasidiagonal, hence amenable. -/
theorem isAmenableTrace_complex : IsAmenableTrace (fun z : ℂ ↦ z) :=
  isAmenableTrace_of_isQuasidiagonalTrace isQuasidiagonalTrace_complex

end

end Quasidiagonal

namespace QuasidiagonalMF

open ReducedGroupCStarTrace

noncomputable section

/-! ## Ingredient 2: every trace on a nuclear algebra is amenable -/

/-- **Nuclear ⟹ every trace is amenable, as a typed input.**

For a nuclear C⋆-algebra the identity factors approximately through matrix
algebras by unital completely positive maps, and the resulting maps are
approximately multiplicative in the `2`-norm of any trace; that a trace on a
nuclear algebra is amenable in the sense of `Quasidiagonal.IsAmenableTrace` is
due to Connes and Haagerup by way of Choi--Effros (see Brown--Ozawa,
Theorem 6.2.7).

It is a **separate citation from Tikuisis--White--Winter**, and separating it
is the point: `TikuisisWhiteWinterInput` bundled the two, so a reader could
not see that the amenability of the trace --- which is where nuclearity is
used --- is not part of the Annals paper's own theorem.

No inhabitant is constructed here.  The repository's own completely positive
approximation property (`CStarExactness.IsNuclearCStarAlgebra`) is the
hypothesis, which is the form the Følner construction of
`Analysis.LanceNuclearAmenable` produces. -/
structure NuclearAmenableTraceInput : Prop where
  /-- Every faithful trace on a nuclear C⋆-algebra is an amenable trace. -/
  amenableTrace : ∀ (A : Type u) (_ : CStarAlgebra A),
    CStarExactness.IsNuclearCStarAlgebra A →
      ∀ τ : FaithfulTracialState A,
        Quasidiagonal.IsAmenableTrace (fun a : A ↦ τ a)

/-! ## Ingredient 3: the Annals theorem itself -/

/-- **Tikuisis--White--Winter, Theorem A, as a typed input --- the actual
statement.**

A faithful **amenable** trace on a separable nuclear C⋆-algebra satisfying the
UCT is **locally** quasidiagonal.

Two differences from `TikuisisWhiteWinterInput`, both of which make this the
weaker assumption:

* it hypothesizes `IsAmenableTrace`, as the paper does, rather than deriving
  it from nuclearity inside the input (that is ingredient 2, a separate
  theorem by separate authors);
* it concludes `IsLocallyQuasidiagonalTrace`, the finite-set/`ε` form the
  paper proves, rather than the sequence form, which needs a diagonal argument
  over a countable dense set (that is ingredient 4, proved in
  `Analysis.QuasidiagonalTraceLocal`).

**No inhabitant is constructed anywhere in this repository, and none can be
without formalizing `KK`-theory, the universal coefficient theorem and the
Dadarlat--Eilers stable uniqueness theorem.**  See the module docstring for
the full list of what the published proof consumes.  It is a structure so that
consuming it leaves a visible binder in the type of every theorem that does. -/
structure TikuisisWhiteWinterCoreInput (UCT : Type u → Prop) : Prop where
  /-- A faithful amenable trace on a separable nuclear UCT C⋆-algebra is
  locally quasidiagonal. -/
  locallyQuasidiagonal : ∀ (A : Type u) (_ : CStarAlgebra A),
    TopologicalSpace.SeparableSpace A →
      CStarExactness.IsNuclearCStarAlgebra A →
        UCT A →
          ∀ τ : FaithfulTracialState A,
            Quasidiagonal.IsAmenableTrace (fun a : A ↦ τ a) →
              Quasidiagonal.IsLocallyQuasidiagonalTrace (fun a : A ↦ τ a)

/-! ## The assembly -/

/-- **The conclusion of `TikuisisWhiteWinterInput`, from the two finer inputs
and one proof.**

Given the Connes--Haagerup input and the Annals theorem in its own form, a
faithful trace on a separable nuclear UCT C⋆-algebra is quasidiagonal in the
sequence sense.  The step that is *not* a citation is the last one: the
diagonal argument of
`Quasidiagonal.isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace`, which
exhausts the separable algebra by a dense sequence and pays for continuity of
`τ` out of the models rather than out of a state-theoretic input.

**Stated pointwise and not as a producer of `TikuisisWhiteWinterInput`**, for
the reason the module docstring gives.  A reader who wants that structure
obtains it by universally quantifying this statement, which asserts nothing
further. -/
theorem isQuasidiagonalTrace_of_core {UCT : Type u → Prop}
    (connes : NuclearAmenableTraceInput.{u})
    (core : TikuisisWhiteWinterCoreInput.{u} UCT)
    (A : Type u) [CStarAlgebra A]
    (hsep : TopologicalSpace.SeparableSpace A)
    (hnuc : CStarExactness.IsNuclearCStarAlgebra A)
    (huct : UCT A) (τ : FaithfulTracialState A) :
    Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a) :=
  Quasidiagonal.isQuasidiagonalTrace_of_isLocallyQuasidiagonalTrace hsep
    (core.locallyQuasidiagonal A inferInstance hsep hnuc huct τ
      (connes.amenableTrace A inferInstance hnuc τ))

/-- **`INT.11`, group by group, over the finer inputs.**

Every countable amenable group is operator-MF, granting: Connes--Haagerup,
the Annals theorem in its own form, Lance's nuclearity theorem and Tu's UCT.
This is `isOperatorMF_of_isAmenable_of_tww` with its third input replaced by
the two ingredients it bundles, with the diagonal argument moved out of the
citation and into the proof, and with the ucp binder discharged by
`Quasidiagonal.ucpContractive`.

Separability and faithfulness of the canonical trace are the repository's own
theorems, as before. -/
theorem isOperatorMF_of_isAmenable_of_core {UCT : Type u → Prop}
    (connes : NuclearAmenableTraceInput.{u})
    (core : TikuisisWhiteWinterCoreInput.{u} UCT)
    (lance : AmenableNuclearInput.{u}) (tu : AmenableUCTInput.{u} UCT)
    (G : Type u) [Group G] [Countable G]
    (hA : Amenability.IsAmenable G) :
    IsOperatorMF G :=
  isOperatorMF_of_isQuasidiagonalCanonicalTrace Quasidiagonal.ucpContractive G
    (isQuasidiagonalTrace_of_core connes core (ReducedGroupCStar G)
      (ReducedGroupCStarTrace.reducedGroupCStar_separableSpace G)
      (lance.nuclear G inferInstance hA) (tu.uct G inferInstance hA)
      (ReducedGroupCStarTrace.canonicalFaithfulTracialState G))

/-! ## The theorem itself, as a proposition one can point at -/

/-- **The Tikuisis--White--Winter theorem, written out as a Lean
proposition**: *every faithful trace on a separable nuclear C⋆-algebra
satisfying the UCT is quasidiagonal.*

Until now the statement existed in this repository only as a **field** of
`TikuisisWhiteWinterInput`, which means a reader could not name it, quantify
over it, or state anything *about* it --- only assume the structure carrying
it.  This is the same proposition, standing alone;
`tikuisisWhiteWinterStatement_iff_input` proves the two are equivalent, so
nothing is smuggled in or left out by the change of shape.

**This is a definition, not a theorem, and it has no proof anywhere.**  What
is formalized here is the *statement*; the *proof* is Tikuisis--White--Winter's
and is not reproducible in this development --- see the module docstring for
the list of what it consumes.  Writing the statement down is worth doing
anyway: it is what lets `tikuisisWhiteWinterStatement_of_core` say precisely
which weaker assumptions imply it, and it gives the proof ledger and the
literature-quarantine gate an object to name.

**Roster obligation.**  This is a corpus-defined `Prop` whose content is a
theorem the repository does not prove, so it belongs on `literaturePackages`
in `scripts/Audit.lean`, together with `TikuisisWhiteWinterCoreInput` and
`NuclearAmenableTraceInput`.  That edit is *not* made here, because
`scripts/Audit.lean` is a shared file and the three names do not exist in any
compiled tree yet; it is recorded in `notes/TWW_REDUCTION_WAVE.md` as the
first thing to do once these modules build. -/
def TikuisisWhiteWinterStatement (UCT : Type u → Prop) : Prop :=
  ∀ (A : Type u) (_ : CStarAlgebra A),
    TopologicalSpace.SeparableSpace A →
      CStarExactness.IsNuclearCStarAlgebra A →
        UCT A →
          ∀ τ : FaithfulTracialState A,
            Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a)

/-- The standalone proposition and the input structure carry the same
content. -/
theorem tikuisisWhiteWinterStatement_iff_input (UCT : Type u → Prop) :
    TikuisisWhiteWinterStatement UCT ↔ TikuisisWhiteWinterInput UCT :=
  ⟨fun h ↦ ⟨h⟩, fun h ↦ h.quasidiagonalTrace⟩

/-- **The theorem follows from the two finer inputs.**  This is
`isQuasidiagonalTrace_of_core` read as a statement about the named
proposition, and it is the precise sense in which this file "takes the
citation apart": granting Connes--Haagerup and the Annals theorem *in its own
form*, the packaged statement is a consequence rather than an assumption.

It is **not** a proof of `TikuisisWhiteWinterStatement`; it is a proof of an
implication whose antecedent contains the irreducible ingredient.  Nothing in
this repository inhabits `TikuisisWhiteWinterCoreInput`. -/
theorem tikuisisWhiteWinterStatement_of_core {UCT : Type u → Prop}
    (connes : NuclearAmenableTraceInput.{u})
    (core : TikuisisWhiteWinterCoreInput.{u} UCT) :
    TikuisisWhiteWinterStatement UCT :=
  fun A inst hsep hnuc huct τ ↦
    @isQuasidiagonalTrace_of_core UCT connes core A inst hsep hnuc huct τ

/-! ## What the two inputs are equivalent to -/

/-- **The two finer inputs together give the packaged one, pointwise.**  The
converse direction --- that `TikuisisWhiteWinterInput` gives the core input
--- is *false* as stated, because the core input's conclusion is the local
form at amenable traces and the packaged one says nothing about traces that
are not known to be faithful-on-a-nuclear-algebra.  What is true, and is the
useful direction, is that a reader who has granted the packaged input has
granted everything the finer pair grants; that is exactly
`isQuasidiagonalTrace_of_core` compared with
`TikuisisWhiteWinterInput.quasidiagonalTrace`.

Recorded as a theorem about one algebra at a time, again to stay out of the
discharge fixpoint. -/
theorem quasidiagonalTrace_of_tww {UCT : Type u → Prop}
    (tww : TikuisisWhiteWinterInput UCT)
    (A : Type u) [CStarAlgebra A]
    (hsep : TopologicalSpace.SeparableSpace A)
    (hnuc : CStarExactness.IsNuclearCStarAlgebra A)
    (huct : UCT A) (τ : FaithfulTracialState A) :
    Quasidiagonal.IsQuasidiagonalTrace (fun a : A ↦ τ a) :=
  tww.quasidiagonalTrace A inferInstance hsep hnuc huct τ

end

end QuasidiagonalMF
end GroupApproximation
