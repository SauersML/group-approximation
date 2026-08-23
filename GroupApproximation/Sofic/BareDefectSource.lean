import GroupApproximation.Sofic.SmallCancellationRouter
import GroupApproximation.Sofic.ConcreteCompressionSource
import GroupApproximation.Kazhdan.IntegerNotKazhdan
import GroupApproximation.GroupTheory.HNNBrittonCyclic
import GroupApproximation.Sofic.ExplicitSuitableDefect

/-!
# The slimmed defect source: what the non-MF endpoint actually consumes

`FournierFacioDefectData` bundles four fields that record the embedded
infinite simple factor — `simpleSubgroup`, its `IsSimpleGroup` instance,
`s_mem` and `witness_mem`.  A consumer trace through

  `RoutingLemmaData` → `DefectRoutingData` → `FiveConditionRoutingData`
  → `Analysis/TorsionFreeFullMFCStarConsequences`

shows that **none of the four is read anywhere on that chain**.  They are
read in exactly two places, both off it: `HullSuitableDefectSubgroup`
(`s_mem_defectNormal`, `witness_mem_defectNormal`, and the
noncommutativity of the defect that Hull's Lemma 5.8 wants) and
`HereditaryNonsoficDescent` (the simple factor embeds in every nontrivial
quotient, which is the *nonsoficity* half of the manuscript).  The
non-MF half needs only that the protected element is nontrivial, and
`FournierFacioDefectData.s_ne_one` derives that from the marked
commutator alone.

`BareDefectSourceData` is therefore `FournierFacioDefectData` with those
four fields deleted and nothing else changed, and `BareRoutingData` is
the routing output over it.  The whole full-radical consequence package
is re-derived here, so a construction that produces no simple subgroup —
which is every bespoke small-cancellation router, since `C'(1/6)`
quotients are not simple — still reaches the endpoint.

**Property `(T)` of the compressed base is NOT deleted, and cannot be.**
It looks vestigial from the routing side, because the routed quotient
receives `(T)` from the Kazhdan partner through `RoutingLemmaData.kazhdan`
and the normal-Kazhdan hypothesis is discharged at `K = ⊤`.  It is not:
the analytic mechanism reads it.  Following
`FiveConditionRoutingData.coronaMFResidual_eq_top` down,

  `KazhdanCompressionCore.normalKazhdan_le_coronaMFResidual`
  → `normalKazhdan_le_normMFResidual`
  → `not_isWeakMF_of_normalKazhdan_le_defect`
  → `compressionDefects_eq_one_in_hyperlinearHom`
  → `compressionDefects_hsTrivial`
  → `KazhdanCompressorCorner.compressionDefect_hsDistSq_vanishing`
  → `transportedRoot_displacement_hsDistSq_vanishing`,

and that last theorem opens by extracting a symmetric generating pair
with a spectral gap from `C.kazhdan` — property `(T)` of the *base*, not
of the quotient.  It is the gap that captures the transported root, so a
compression core over an amenable base proves nothing.  The bookkeeping
matches the mathematics: an ascending HNN extension over `ℤ` is a
Baumslag--Solitar group, hence amenable, hence MF.  The last section of
this file records that obstruction as a theorem rather than a remark.

So the slimming removes the simple-factor demand from the source and
leaves the demand that survives: a property-`(T)` group with a proper
self-embedding, a centralizing root, and a nontrivial marked commutator.

Nothing here edits or replaces the existing lane.
`DefectRoutingData.toBareRoutingData` certifies that the old interface
factors through the new one, so this layer is a generalization and not a
fork.
-/

namespace GroupApproximation

open scoped commutatorElement

universe u

/-! ## The slimmed source datum -/

/-- **`FournierFacioDefectData` with the simple-factor fields deleted.**

The remaining fields are exactly the ones the compression core and the
protected element are built from: the property-`(T)` base map `iota`, the
stable letter `u`, the transported root `s`, the compression relation,
the commutation relation `[s, u ι(p) u⁻¹] = 1`, and one base element
whose marked commutator with `s` is nontrivial.

There is no `simpleSubgroup`, no `IsSimpleGroup`, no `s_mem` and no
`witness_mem`; the consumer trace in the module docstring shows the
non-MF endpoint reads none of them.  There is still a `kazhdan` field,
because the analytic mechanism does read that one. -/
structure BareDefectSourceData (P : Type) (E : Type u) [Group P] [Group E] where
  /-- The property-`(T)` base map. -/
  iota : P →* E
  /-- The first stable letter. -/
  u : E
  /-- The protected element: the transported root of the hidden pattern. -/
  s : E
  /-- Property `(T)` of the base.  Load-bearing: the root-capture step of
  the analytic obstruction extracts a Kazhdan pair from it. -/
  kazhdan : HasKazhdanPropertyT.{0, 0} P
  /-- Conjugation by `u` compresses the base into itself. -/
  compresses : ∀ p : P, ∃ q : P, u * iota p * u⁻¹ = iota q
  /-- The protected element commutes with the compressed base. -/
  commutesAfterCompression :
    ∀ p : P, Commute s (u * iota p * u⁻¹)
  /-- A base element witnessing that the protected element is not central. -/
  witness : P
  /-- The chosen marked commutator is nontrivial. -/
  witness_commutator_ne_one : ⁅s, iota witness⁆ ≠ 1

namespace BareDefectSourceData

variable {P : Type} {E : Type u} [Group P] [Group E]
    (D : BareDefectSourceData P E)

/-- The marked Kazhdan-compression core carried by the slimmed datum.  Its
root is `u⁻¹ s u`, so transporting the root by `u` recovers `s`.  This is
field-for-field the core of `FournierFacioDefectData`, which is why
`FournierFacioDefectData.toBareDefectSourceData_core` is `rfl`. -/
def core : KazhdanCompressionCore P E where
  iota := D.iota
  t := D.u
  c := D.u⁻¹ * D.s * D.u
  kazhdan := D.kazhdan
  compresses := D.compresses
  comm_c p := by
    show D.u⁻¹ * D.s * D.u * D.iota p =
      D.iota p * (D.u⁻¹ * D.s * D.u)
    have h := (D.commutesAfterCompression p).eq
    calc
      D.u⁻¹ * D.s * D.u * D.iota p =
          D.u⁻¹ * (D.s * (D.u * D.iota p * D.u⁻¹)) * D.u := by
            group
      _ = D.u⁻¹ * ((D.u * D.iota p * D.u⁻¹) * D.s) * D.u := by
            rw [h]
      _ = D.iota p * (D.u⁻¹ * D.s * D.u) := by
            group

/-- The transported root of the hidden pattern is the protected element. -/
@[simp] theorem core_transported : D.core.transported = D.s := by
  unfold core KazhdanCompressionCore.transported
  dsimp
  group

/-- The defect is exactly the normal closure of the marked commutators
`[s, ι(p)]`. -/
theorem core_defectNormal_eq :
    D.core.defectNormal =
      Subgroup.normalClosure (Set.range fun p : P ↦ ⁅D.s, D.iota p⁆) := by
  unfold KazhdanCompressionCore.defectNormal
    KazhdanCompressionCore.defectSet
  rw [D.core_transported]
  rfl

/-- The chosen nontrivial commutator lies in the compression defect. -/
theorem witness_commutator_mem_defectNormal :
    ⁅D.s, D.iota D.witness⁆ ∈ D.core.defectNormal := by
  rw [← D.core_transported]
  exact D.core.defect_mem_defectNormal D.witness

/-- **A base-surjective image cannot see the compression defect.**

If `f ∘ ι` already maps the Kazhdan base onto a target group, then the
image of the compressed base is onto as well: it is just the conjugate by
`f(u)` of the image of the base.  Since `s` centralizes that compressed
copy, `f(s)` centralizes the whole target.  Consequently every marked
commutator, and hence its normal closure, lies in `ker f`.

This is the elementary obstruction to adjoining a direct or diagonal
property-`(T)` factor and hoping that factor lies in the defect: whenever
the factor is already a quotient of the source copy, the defect has trivial
projection to it. -/
theorem core_defectNormal_le_ker_of_iota_surjective
    {Q : Type*} [Group Q] (f : E →* Q)
    (hsurj : Function.Surjective (f.comp D.iota)) :
    D.core.defectNormal ≤ f.ker := by
  rw [D.core_defectNormal_eq]
  apply Subgroup.normalClosure_le_normal
  rintro x ⟨p, rfl⟩
  apply MonoidHom.mem_ker.mpr
  rw [map_commutatorElement]
  apply commutatorElement_eq_one_iff_commute.mpr
  obtain ⟨q, hq⟩ := hsurj ((f D.u)⁻¹ * f (D.iota p) * f D.u)
  have hcompressed :
      f (D.u * D.iota q * D.u⁻¹) = f (D.iota p) := by
    simp only [map_mul, map_inv]
    change f (D.iota q) = _ at hq
    rw [hq]
    group
  have hcomm := (D.commutesAfterCompression q).map f
  rwa [hcompressed] at hcomm

/-- The protected element is nontrivial.  This is the only consequence of
the marked commutator that the non-MF chain uses, and it needs no simple
subgroup: were `s` trivial its commutators would be too. -/
theorem s_ne_one : D.s ≠ 1 := by
  intro hs
  apply D.witness_commutator_ne_one
  rw [hs]
  simp

/-- An injective homomorphism of ambient groups transports every clause of a
slimmed defect source.  Injectivity is used only once, to reflect
nontriviality of the protected commutator; all displayed HNN relations simply
map forward. -/
def mapAmbient {F : Type*} [Group F] (f : E →* F)
    (hf : Function.Injective f) : BareDefectSourceData P F where
  iota := f.comp D.iota
  u := f D.u
  s := f D.s
  kazhdan := D.kazhdan
  compresses := by
    intro p
    obtain ⟨q, hq⟩ := D.compresses p
    refine ⟨q, ?_⟩
    simpa using congrArg f hq
  commutesAfterCompression := by
    intro p
    simpa using (D.commutesAfterCompression p).map f
  witness := D.witness
  witness_commutator_ne_one := by
    intro h
    apply D.witness_commutator_ne_one
    apply hf
    simpa only [map_commutatorElement, MonoidHom.comp_apply, map_one] using h

end BareDefectSourceData

/-! ## Exact comparison with the Fournier--Facio source

`BareDefectSourceData` is not merely analogous to
`FournierFacioDefectData`: the latter is obtained by adjoining exactly one
small package.  Keeping that package separate is useful for construction
work, because it prevents the four simple-factor clauses (which the non-MF
endpoint does not consume) from being confused with any of the compression
relations.
-/

/-- The exact extra data needed to upgrade a slimmed defect source to the
original Fournier--Facio interface.

There are only three mathematical clauses: a simple subgroup containing the
protected element and the image of the chosen witness.  The `simple` field is
the typeclass-form proof attached to that subgroup.  Every other field of
`FournierFacioDefectData` is already a field of `D`. -/
structure FournierFacioSimpleFactorCompletion
    {P : Type} {E : Type u} [Group P] [Group E]
    (D : BareDefectSourceData P E) where
  simpleSubgroup : Subgroup E
  [simple : IsSimpleGroup simpleSubgroup]
  s_mem : D.s ∈ simpleSubgroup
  witness_mem : D.iota D.witness ∈ simpleSubgroup

namespace BareDefectSourceData

variable {P : Type} {E : Type u} [Group P] [Group E]
    (D : BareDefectSourceData P E)

/-- Adjoining a simple-factor completion recovers the original
Fournier--Facio defect datum, with no further hypothesis. -/
def toFournierFacioDefectData
    (C : FournierFacioSimpleFactorCompletion D) :
    FournierFacioDefectData P E where
  iota := D.iota
  u := D.u
  s := D.s
  kazhdan := D.kazhdan
  compresses := D.compresses
  commutesAfterCompression := D.commutesAfterCompression
  simpleSubgroup := C.simpleSubgroup
  simple := C.simple
  s_mem := C.s_mem
  witness := D.witness
  witness_mem := C.witness_mem
  witness_commutator_ne_one := D.witness_commutator_ne_one

end BareDefectSourceData

/-! ## Both existing sources land on the slimmed datum -/

/-- Deleting the four simple-factor fields of a Fournier--Facio defect
datum leaves a slimmed source datum. -/
def FournierFacioDefectData.toBareDefectSourceData
    {P : Type} {E : Type u} [Group P] [Group E]
    (D : FournierFacioDefectData P E) : BareDefectSourceData P E where
  iota := D.iota
  u := D.u
  s := D.s
  kazhdan := D.kazhdan
  compresses := D.compresses
  commutesAfterCompression := D.commutesAfterCompression
  witness := D.witness
  witness_commutator_ne_one := D.witness_commutator_ne_one

/-- Upgrading a slimmed source by exactly its simple-factor fields and then
forgetting those fields returns the original source definitionally. -/
@[simp] theorem BareDefectSourceData.toFournierFacioDefectData_toBareDefectSourceData
    {P : Type} {E : Type u} [Group P] [Group E]
    (D : BareDefectSourceData P E)
    (C : FournierFacioSimpleFactorCompletion D) :
    (D.toFournierFacioDefectData C).toBareDefectSourceData = D := rfl

/-- Deleting the simple-factor fields does not move the compression core. -/
@[simp] theorem FournierFacioDefectData.toBareDefectSourceData_core
    {P : Type} {E : Type u} [Group P] [Group E]
    (D : FournierFacioDefectData P E) :
    D.toBareDefectSourceData.core = D.core := rfl

/-- Nor does it move the protected element. -/
@[simp] theorem FournierFacioDefectData.toBareDefectSourceData_s
    {P : Type} {E : Type u} [Group P] [Group E]
    (D : FournierFacioDefectData P E) :
    D.toBareDefectSourceData.s = D.s := rfl

/-- **A concrete source upgrades exactly when its base is Kazhdan.**
`ConcreteCompressionSource.CompressionSourceData` carries every field of
the slimmed datum except property `(T)` of the base, so supplying `(T)`
is the only step between the two interfaces.

Read that as a statement about the interfaces, not as a to-do item on the
source we actually have.  For `ConcreteCompressionSource.integerSource`
the missing field is not merely unproved, it is unobtainable: the base is
`Multiplicative ℤ`, and `isEmpty_bareDefectSourceData_multiplicative_int`
below rules out every slimmed source over it.  So what remains is not a
field to fill in on the existing skeleton but a genuinely new Kazhdan
base carrying a proper self-compression, with the concrete affine-HNN
construction re-run over it. -/
def ConcreteCompressionSource.CompressionSourceData.toBareDefectSourceData
    {P : Type} {E : Type u} [Group P] [Group E]
    (d : ConcreteCompressionSource.CompressionSourceData P E)
    (hT : HasKazhdanPropertyT.{0, 0} P) : BareDefectSourceData P E where
  iota := d.iota
  u := d.u
  s := d.s
  kazhdan := hT
  compresses := d.compresses
  commutesAfterCompression := d.commutesAfterCompression
  witness := d.witness
  witness_commutator_ne_one := d.witness_commutator_ne_one

/-- The upgrade is compatible with the two compression cores. -/
@[simp] theorem ConcreteCompressionSource.CompressionSourceData.toBareDefectSourceData_core
    {P : Type} {E : Type u} [Group P] [Group E]
    (d : ConcreteCompressionSource.CompressionSourceData P E)
    (hT : HasKazhdanPropertyT.{0, 0} P) :
    (d.toBareDefectSourceData hT).core = d.core hT := rfl

/-! ## Routing over the slimmed source -/

/-- **`DefectRoutingData` over the slimmed source.**

Field for field this is `DefectRoutingData`, with two differences.  The
indexing datum carries no simple subgroup, and surjectivity of the
routing map is not stored: `quotient_surjective` derives it from
`defect_surjective` exactly as `FiveConditionRoutingData` does, so this
interface assumes strictly less than the old one on that point too.

The survival field `protected_ne_one` is kept, because it is what makes
the routed quotient itself non-MF rather than only its nontrivial
quotients; `SmallCancellationRouter.RoutingLemmaData.toBareRoutingData`
derives it from injectivity on the protected set, so no construction has
to postulate it. -/
structure BareRoutingData {P : Type} {E : Type u} [Group P] [Group E]
    (D : BareDefectSourceData P E) where
  /-- The routed common quotient. -/
  Quotient : Type
  [groupQuotient : Group Quotient]
  /-- The quotient map from the source. -/
  quotient : E →* Quotient
  /-- The routed quotient is finitely presented. -/
  [finitelyPresented : Group.IsFinitelyPresented Quotient]
  /-- Property `(T)`, obtained from the Kazhdan partner's surjection. -/
  kazhdan : HasKazhdanPropertyT.{0, 0} Quotient
  /-- Hull's torsion-preservation conclusion, in power form. -/
  torsionFree : IsPowerTorsionFree Quotient
  /-- First generator produced by the routing stage. -/
  generatorOne : Quotient
  /-- Second generator produced by the routing stage. -/
  generatorTwo : Quotient
  /-- The two routed elements generate the quotient. -/
  generates :
    Subgroup.closure ({generatorOne, generatorTwo} : Set Quotient) = ⊤
  /-- The compression defect maps onto the whole quotient. -/
  defect_surjective : D.core.defectNormal.map quotient = ⊤
  /-- The protected element survives. -/
  protected_ne_one : quotient D.s ≠ 1

namespace BareRoutingData

variable {P : Type} {E : Type u} [Group P] [Group E]
    {D : BareDefectSourceData P E}
    (R : BareRoutingData.{u} D)

local instance bareRoutedQuotientGroup : Group R.Quotient := R.groupQuotient
local instance bareRoutedQuotientFinitelyPresented :
    Group.IsFinitelyPresented R.Quotient := R.finitelyPresented

/-- Surjectivity of the routing map is not an extra assumption: the defect
already maps onto everything. -/
theorem quotient_surjective : Function.Surjective R.quotient := by
  intro y
  have hy : y ∈ D.core.defectNormal.map R.quotient := by
    rw [R.defect_surjective]
    exact Subgroup.mem_top y
  obtain ⟨x, -, hx⟩ := Subgroup.mem_map.mp hy
  exact ⟨x, hx⟩

/-- A finitely presented routed quotient is countable. -/
theorem quotientCountable : Countable R.Quotient := by
  obtain ⟨n, f, hsurj, -⟩ := R.finitelyPresented.out
  letI : Countable (FreeGroup (Fin n)) := by
    have hfree : Function.Surjective
        (FreeGroup.mk : List (Fin n × Bool) → FreeGroup (Fin n)) := by
      intro g
      obtain ⟨L, hL⟩ := Quot.exists_rep g
      exact ⟨L, by rw [← FreeGroup.quot_mk_eq_mk, hL]⟩
    exact hfree.countable
  exact hsurj.countable

local instance bareRoutedQuotientCountable : Countable R.Quotient :=
  R.quotientCountable

/-- The structure's two chosen elements witness two-generation. -/
theorem isTwoGenerated : IsTwoGenerated R.Quotient :=
  ⟨R.generatorOne, R.generatorTwo, R.generates⟩

/-- The routed quotient is nontrivial because the protected element
survives. -/
theorem quotientNontrivial : Nontrivial R.Quotient :=
  ⟨⟨R.quotient D.s, 1, R.protected_ne_one⟩⟩

/-- Defect routing commutes with descent of the marked pattern: the defect
of the mapped core is the whole quotient. -/
theorem mapped_defectNormal_eq_top :
    (D.core.map R.quotient).defectNormal = ⊤ := by
  apply top_unique
  rw [← R.defect_surjective]
  exact D.core.map_subgroup_le_defectNormal R.quotient
    D.core.defectNormal le_rfl

/-- **Full MF radical.**  Every element of the routed quotient is invisible
in every standard cofinite norm-matrix corona.  Property `(T)` of the
quotient and saturation of the defect are the only routing inputs; property
`(T)` of the base enters inside the analytic obstruction. -/
theorem coronaMFResidual_eq_top :
    coronaMFResidual R.Quotient = ⊤ := by
  letI : Countable R.Quotient := R.quotientCountable
  have hTtop :
      HasKazhdanPropertyT.{0, 0} (⊤ : Subgroup R.Quotient) :=
    HasKazhdanPropertyT.of_mulEquiv Subgroup.topEquiv R.kazhdan
  have htop_le : (⊤ : Subgroup R.Quotient) ≤
      coronaMFResidual R.Quotient := by
    apply KazhdanCompressionCore.normalKazhdan_le_coronaMFResidual
      (D.core.map R.quotient) (⊤ : Subgroup R.Quotient) hTtop
    rw [R.mapped_defectNormal_eq_top]
  exact top_unique htop_le

/-- **Literal CDE full radical.** -/
theorem cdeMFResidual_eq_top : cdeMFResidual R.Quotient = ⊤ := by
  rw [cdeMFResidual_eq_coronaMFResidual]
  exact R.coronaMFResidual_eq_top

/-- Ultraproduct-language form of the full-radical theorem. -/
theorem normMFResidual_eq_top :
    normMFResidual R.Quotient = ⊤ := by
  letI : Countable R.Quotient := R.quotientCountable
  rw [← coronaMFResidual_eq_normMFResidual]
  exact R.coronaMFResidual_eq_top

/-- Every representation of the routed quotient in a standard cofinite
norm-matrix corona is the trivial homomorphism. -/
theorem coronaRepresentation_eq_one
    (X : ℕ → FiniteModel) (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : R.Quotient →* NormMatrixCoronaUnitary X) : rho = 1 := by
  apply MonoidHom.ext
  intro g
  have hg : g ∈ coronaMFResidual R.Quotient := by
    rw [R.coronaMFResidual_eq_top]
    exact Subgroup.mem_top g
  exact hg X hX rho

/-- **Every homomorphism to a matrix quotient is trivial.** -/
theorem cdeCoronaRepresentation_eq_one
    (X : ℕ → FiniteModel) [∀ n, Nonempty (X n)]
    (hX : ∀ n, 0 < Fintype.card (X n))
    (rho : R.Quotient →*
      unitary (NormMatrixCStarCorona (fun n ↦ X n))) : rho = 1 := by
  let sigma : R.Quotient →* NormMatrixCoronaUnitary X :=
    (normMatrixCoronaUnitaryEquiv X).symm.toMonoidHom.comp rho
  have hsigma : sigma = 1 := R.coronaRepresentation_eq_one X hX sigma
  apply MonoidHom.ext
  intro g
  apply (normMatrixCoronaUnitaryEquiv X).symm.injective
  simpa [sigma] using DFunLike.congr_fun hsigma g

/-- Every homomorphism from the routed quotient to any operator-MF group is
trivial.  The target need not be countable. -/
theorem hom_eq_one_to_isOperatorMF
    {M : Type*} [Group M] (hM : IsOperatorMF M)
    (f : R.Quotient →* M) : f = 1 := by
  letI : Countable R.Quotient := R.quotientCountable
  apply MonoidHom.ext
  intro g
  exact map_eq_one_of_normMFResidual_eq_top_to_isOperatorMF
    R.normMFResidual_eq_top hM f g

/-- Every homomorphism from the routed quotient to a finite group is
trivial. -/
theorem hom_eq_one_to_finite
    (M : Type) [Group M] [Finite M] (f : R.Quotient →* M) : f = 1 :=
  hom_eq_one_of_residual_eq_top_to_finite R.normMFResidual_eq_top M f

/-- Every homomorphism from the routed quotient to a countable residually
finite group is trivial. -/
theorem hom_eq_one_to_residuallyFinite
    {M : Type*} [Group M] [Countable M] [Group.ResiduallyFinite M]
    (f : R.Quotient →* M) : f = 1 :=
  hom_eq_one_of_residual_eq_top_to_residuallyFinite
    R.normMFResidual_eq_top f

/-- The routed quotient has no nontrivial finite quotient. -/
theorem no_nontrivial_finite_quotient
    (M : Type) [Group M] [Finite M] [Nontrivial M]
    (f : R.Quotient →* M) : ¬ Function.Surjective f :=
  not_surjective_of_residual_eq_top_to_finite
    R.normMFResidual_eq_top M f

/-- Every quotient of the routed group again has full corona MF radical. -/
theorem quotient_coronaMFResidual_eq_top
    {H : Type*} [Group H] (q : R.Quotient →* H)
    (hq : Function.Surjective q) : coronaMFResidual H = ⊤ := by
  letI : Countable R.Quotient := R.quotientCountable
  exact coronaMFResidual_eq_top_of_surjective
    R.coronaMFResidual_eq_top q hq

/-- Every quotient of the routed group has full ultraproduct norm-MF
residual as well. -/
theorem quotient_normMFResidual_eq_top
    {H : Type*} [Group H] (q : R.Quotient →* H)
    (hq : Function.Surjective q) : normMFResidual H = ⊤ := by
  letI : Countable R.Quotient := R.quotientCountable
  letI : Countable H := hq.countable
  rw [← coronaMFResidual_eq_normMFResidual]
  exact R.quotient_coronaMFResidual_eq_top q hq

/-- **Every nontrivial quotient fails to be MF.** -/
theorem quotient_not_isOperatorMF
    {H : Type*} [Group H] [Nontrivial H]
    (q : R.Quotient →* H) (hq : Function.Surjective q) :
    ¬ IsOperatorMF H := by
  letI : Countable R.Quotient := R.quotientCountable
  letI : Countable H := hq.countable
  intro hMF
  have htop : coronaMFResidual H = ⊤ :=
    R.quotient_coronaMFResidual_eq_top q hq
  have hbot : coronaMFResidual H = ⊥ :=
    isOperatorMF_iff_coronaMFResidual_eq_bot.mp hMF
  obtain ⟨x, hx⟩ := exists_ne (1 : H)
  have hxres : x ∈ coronaMFResidual H := by
    rw [htop]
    exact Subgroup.mem_top x
  rw [hbot] at hxres
  exact hx (Subgroup.mem_bot.mp hxres)

/-- Literal CDE form of the hereditary statement. -/
theorem quotient_not_isCDEOperatorMF
    {H : Type*} [Group H] [Countable H] [Nontrivial H]
    (q : R.Quotient →* H) (hq : Function.Surjective q) :
    ¬ IsCDEOperatorMF H := by
  rw [isCDEOperatorMF_iff_isOperatorMF]
  exact R.quotient_not_isOperatorMF q hq

/-- The routed quotient is not operator-MF.  Unlike everything above, this
uses the survival field: without it the routed quotient could be trivial,
and the trivial group is MF. -/
theorem not_isOperatorMF : ¬ IsOperatorMF R.Quotient := by
  intro hMF
  have htrivial : MonoidHom.id R.Quotient = 1 :=
    R.hom_eq_one_to_isOperatorMF hMF (MonoidHom.id R.Quotient)
  apply R.protected_ne_one
  simpa using DFunLike.congr_fun htrivial (R.quotient D.s)

/-- Literal Carrión--Dadarlat--Eckhardt formulation of the non-MF theorem. -/
theorem not_isCDEOperatorMF : ¬ IsCDEOperatorMF R.Quotient := by
  rw [isCDEOperatorMF_iff_isOperatorMF]
  exact R.not_isOperatorMF

/-- The non-MF theorem is unchanged when the CDE convention requires the
matrix dimensions to be strictly increasing. -/
theorem not_isOperatorMFIncreasing : ¬ IsOperatorMFIncreasing R.Quotient := by
  rw [isOperatorMFIncreasing_iff]
  exact R.not_isOperatorMF

/-- The full consequence package, over a source that carries no simple
subgroup: finite presentation, two-generation, torsion-freeness, property
`(T)`, nontriviality, full CDE-MF radical, and failure of operator-MF. -/
theorem consequence_package :
    Group.IsFinitelyPresented R.Quotient ∧
      IsTwoGenerated R.Quotient ∧
      IsPowerTorsionFree R.Quotient ∧
      HasKazhdanPropertyT.{0, 0} R.Quotient ∧
      Nontrivial R.Quotient ∧
      cdeMFResidual R.Quotient = ⊤ ∧
      ¬ IsOperatorMF R.Quotient ∧
      ¬ IsCDEOperatorMF R.Quotient :=
  ⟨R.finitelyPresented, R.isTwoGenerated, R.torsionFree, R.kazhdan,
    R.quotientNontrivial, R.cdeMFResidual_eq_top, R.not_isOperatorMF,
    R.not_isCDEOperatorMF⟩

end BareRoutingData

/-- **The old interface factors through the new one.**  Every
`DefectRoutingData` over a full Fournier--Facio datum is a
`BareRoutingData` over its slimming, so this file generalizes the routing
layer rather than forking it: anything the old chain proves, the new one
proves too. -/
def DefectRoutingData.toBareRoutingData
    {P : Type} {E : Type u} [Group P] [Group E]
    {D : FournierFacioDefectData P E} (R : DefectRoutingData.{u} D) :
    BareRoutingData D.toBareDefectSourceData where
  Quotient := R.Quotient
  groupQuotient := R.groupQuotient
  quotient := R.quotient
  finitelyPresented := R.finitelyPresented
  kazhdan := R.kazhdan
  torsionFree := R.torsionFree
  generatorOne := R.generatorOne
  generatorTwo := R.generatorTwo
  generates := R.generates
  defect_surjective := R.defect_surjective
  protected_ne_one := R.protected_ne_one

namespace SmallCancellationRouter

/-- **The slimmed keystone.**  The abstract router output, instantiated at
the compression defect and protected element of a *slimmed* source datum,
is exactly the routing data consumed by the full-MF-radical machine.  The
statement is the same as `RoutingLemmaData.toDefectRoutingData` with the
simple-subgroup demand on the source removed: whoever proves the routing
lemma over any property-`(T)` compression source has proved the Main
Theorem, and no infinite simple factor has to be produced anywhere. -/
def RoutingLemmaData.toBareRoutingData
    {P : Type} {E : Type u} [Group P] [Group E]
    (D : BareDefectSourceData P E) {B : Type} [Group B]
    (hB : HasKazhdanPropertyT.{0, 0} B)
    (R : RoutingLemmaData E D.core.defectNormal D.s B) :
    BareRoutingData D where
  Quotient := R.Quotient
  groupQuotient := R.groupQuotient
  quotient := R.route
  finitelyPresented := R.finitelyPresented
  kazhdan := R.kazhdan hB
  torsionFree := R.torsionFree
  generatorOne := R.generatorOne
  generatorTwo := R.generatorTwo
  generates := R.generates
  defect_surjective := R.defect_top
  protected_ne_one := R.route_protected_ne_one D.s_ne_one

/-- Any inhabitant of the abstract router interface at a slimmed source
discharges the slimmed endpoint's single hypothesis. -/
theorem nonempty_bareRoutingData
    {P : Type} {E : Type u} [Group P] [Group E]
    (D : BareDefectSourceData P E) {B : Type} [Group B]
    (hB : HasKazhdanPropertyT.{0, 0} B)
    (h : Nonempty (RoutingLemmaData E D.core.defectNormal D.s B)) :
    Nonempty (BareRoutingData D) := by
  obtain ⟨R⟩ := h
  exact ⟨RoutingLemmaData.toBareRoutingData D hB R⟩

end SmallCancellationRouter

/-! ## The endpoint over the slimmed source -/

namespace BareFullMFRadicalEndpoint

/-- **Conditional output package.**  Given an inhabitant of the still-open
`BareRoutingData` interface, the routed group is nontrivial, two-generated,
finitely presented, torsion-free, property-`(T)`, and has full literal CDE MF
radical.

The routing datum is a genuine hypothesis.  This declaration is deliberately
named `_of_bareRoutingData` and must not be cited as an unconditional existence
theorem. -/
theorem exists_nontrivial_twoGenerated_finitelyPresented_torsionFree_kazhdan_fullMFRadical_of_bareRoutingData :
    ∀ {P : Type} {E : Type u} [Group P] [Group E]
      {D : BareDefectSourceData P E}
      (_h : Nonempty (BareRoutingData.{u} D)),
      ∃ (Q : Type) (_ : Group Q) (_ : Countable Q),
        IsTwoGenerated Q ∧
        Group.IsFinitelyPresented Q ∧
        IsPowerTorsionFree Q ∧
        HasKazhdanPropertyT.{0, 0} Q ∧
        Nontrivial Q ∧
        cdeMFResidual Q = ⊤ := by
  intro P E _ _ D h
  obtain ⟨R⟩ := h
  letI : Group R.Quotient := R.groupQuotient
  letI : Countable R.Quotient := R.quotientCountable
  exact ⟨R.Quotient, inferInstance, inferInstance, R.isTwoGenerated,
    R.finitelyPresented, R.torsionFree, R.kazhdan, R.quotientNontrivial,
    R.cdeMFResidual_eq_top⟩

/-- **Conditional hereditary output package.**  From the same supplied
`BareRoutingData`, every genuine norm-matrix-corona representation of the
output is trivial and every nontrivial quotient fails to be MF. -/
theorem exists_nontrivial_group_with_every_nontrivial_quotient_not_isCDEOperatorMF_of_bareRoutingData :
    ∀ {P : Type} {E : Type u} [Group P] [Group E]
      {D : BareDefectSourceData P E}
      (_h : Nonempty (BareRoutingData.{u} D)),
      ∃ (Q : Type) (_ : Group Q) (_ : Countable Q),
        IsTwoGenerated Q ∧
        Group.IsFinitelyPresented Q ∧
        IsPowerTorsionFree Q ∧
        HasKazhdanPropertyT.{0, 0} Q ∧
        Nontrivial Q ∧
        ¬ IsCDEOperatorMF Q ∧
        (∀ (X : ℕ → FiniteModel) (hne : ∀ n, Nonempty (X n)),
          letI := hne
          (∀ n, 0 < Fintype.card (X n)) →
            ∀ rho : Q →* unitary (NormMatrixCStarCorona (fun n ↦ X n)),
              rho = 1) ∧
        ∀ (H : Type) (_ : Group H) (_ : Countable H) (_ : Nontrivial H)
          (f : Q →* H),
          Function.Surjective f → ¬ IsCDEOperatorMF H := by
  intro P E _ _ D h
  obtain ⟨R⟩ := h
  letI : Group R.Quotient := R.groupQuotient
  letI : Countable R.Quotient := R.quotientCountable
  refine ⟨R.Quotient, inferInstance, inferInstance, R.isTwoGenerated,
    R.finitelyPresented, R.torsionFree, R.kazhdan, R.quotientNontrivial,
    R.not_isCDEOperatorMF, ?_, ?_⟩
  · intro X hne hX rho
    exact R.cdeCoronaRepresentation_eq_one X hX rho
  · intro H _ _ _ f hf
    exact R.quotient_not_isCDEOperatorMF f hf

end BareFullMFRadicalEndpoint

/-! ## What the slimmed source still costs

The two interfaces now differ by exactly one field, and it is the one that
cannot go.  `toCompressionSourceData_toBareDefectSourceData` says so as a
`rfl`: forgetting property `(T)` and putting it back is the identity.

The two theorems after it transport the existing source constraints onto
the slimmed datum, so the irreducible obligation is visible in one place:
the base must be an **infinite** property-`(T)` group carrying a
**strictly proper** self-compression.  That is what a source construction
has to deliver, and no part of it is removed by the slimming. -/

namespace BareDefectSourceData

variable {P : Type} {E : Type u} [Group P] [Group E]
    (D : BareDefectSourceData P E)

/-- Forgetting property `(T)` of the base lands on the concrete
compression source interface. -/
def toCompressionSourceData : ConcreteCompressionSource.CompressionSourceData P E where
  iota := D.iota
  u := D.u
  s := D.s
  compresses := D.compresses
  commutesAfterCompression := D.commutesAfterCompression
  witness := D.witness
  witness_commutator_ne_one := D.witness_commutator_ne_one

/-- **The two interfaces differ by exactly the `(T)` field.**  Forgetting it
and supplying it again is the identity, so nothing else was slimmed away
and nothing else can be. -/
@[simp] theorem toCompressionSourceData_toBareDefectSourceData :
    D.toCompressionSourceData.toBareDefectSourceData D.kazhdan = D := rfl

include D in
/-- **The base of a slimmed source is infinite.**  Transported from
`ConcreteCompressionSource.CompressionSourceData.infinite_source`: the
compression is injective and maps the source copy into itself, so a finite
base would make it onto, which the marked commutator forbids. -/
theorem infinite_source : Infinite P :=
  D.toCompressionSourceData.infinite_source

/-- **The compression is strictly proper.**  So the base is an infinite
property-`(T)` group admitting a proper self-embedding — the irreducible
demand the slimming does not touch. -/
theorem not_conjugation_surjective :
    ¬ ∀ p : P, ∃ q : P, D.u * D.iota q * D.u⁻¹ = D.iota p :=
  D.toCompressionSourceData.not_conjugation_surjective

end BareDefectSourceData

/-! ## Why the integer source cannot be upgraded

`ConcreteCompressionSource.integerSource` is the completely explicit
compression source: the affine HNN skeleton of the doubling map on `ℤ`.
It is unconditional, and its skeleton is torsion-free —
`HNNBritton.isPowerTorsionFree_integerSourceGroup` proves that outright,
so the docstring in `ConcreteCompressionSource` describing the HNN torsion
theorem as "not yet formalized" is stale.

It still cannot feed the endpoint, and the reason is not a missing
formalization: the slimmed datum keeps property `(T)` of the base, and the
base is `ℤ`.  The two theorems below record both halves, so that no later
wave spends effort trying to close a gap that is closed and a gap that is
a theorem in the other direction. -/

/-- **The explicit integer compression source is torsion-free.**  Recorded
in this lane because `ConcreteCompressionSource` still describes this step
as open; it is not. -/
theorem integerSourceGroup_isPowerTorsionFree :
    IsPowerTorsionFree
      (ConcreteCompressionSource.SourceGroup
        ConcreteCompressionSource.doubling
        ConcreteCompressionSource.doubling_injective) :=
  HNNBritton.isPowerTorsionFree_integerSourceGroup

/-- **No slimmed defect source has an infinite cyclic base.**  Property
`(T)` of the base is the one field of `BareDefectSourceData` that the
integer source cannot discharge, and it cannot be dropped: the analytic
obstruction reads it, through
`KazhdanCompressorCorner.transportedRoot_displacement_hsDistSq_vanishing`.
So `ConcreteCompressionSource.integerSource` — and every ascending HNN
skeleton over `ℤ` — is permanently outside the interface, whatever the
ambient group is.  This is the expected answer rather than a defect of the
formalization: an ascending HNN extension over `ℤ` is a Baumslag--Solitar
group, hence amenable, hence MF. -/
theorem isEmpty_bareDefectSourceData_multiplicative_int
    {E : Type u} [Group E] :
    IsEmpty (BareDefectSourceData (Multiplicative ℤ) E) :=
  ⟨fun D => not_hasKazhdanPropertyT_multiplicative_int D.kazhdan⟩

/-! ## The normal defect of a slimmed source -/

namespace BareDefectSourceData

open HullSuitable

variable {P : Type} {E : Type u} [Group P] [Group E]
    (D : BareDefectSourceData P E)

/-- The compression defect is infinite in a torsion-free ambient group. -/
theorem defectNormal_infinite (hE : IsPowerTorsionFree E) :
    Infinite D.core.defectNormal :=
  infinite_of_mem_of_not_isOfFinOrder D.witness_commutator_mem_defectNormal
    (hE.not_isOfFinOrder D.witness_commutator_ne_one)

/-- The compression defect is `s`-normal. -/
theorem defectNormal_isSNormal (hE : IsPowerTorsionFree E) :
    IsSNormal D.core.defectNormal :=
  isSNormal_of_normal_of_mem_not_isOfFinOrder D.core.defectNormal
    D.witness_commutator_mem_defectNormal
    (hE.not_isOfFinOrder D.witness_commutator_ne_one)

/-- Torsion-freeness supplies Hull's finite-normalizer clause. -/
theorem defectNormal_normalizesNoNontrivialFinite
    (hE : IsPowerTorsionFree E) :
    NormalizesNoNontrivialFinite D.core.defectNormal :=
  normalizesNoNontrivialFinite_of_torsionFree hE _

end BareDefectSourceData

end GroupApproximation
