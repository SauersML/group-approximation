import GroupApproximation.Manuscript.NonMF.AcylindricallyHyperbolic
import GroupApproximation.Manuscript.NonMF.FreeCommutatorWitness
import GroupApproximation.Manuscript.NonMF.FournierFacioDoubleHNN
import GroupApproximation.Sofic.ChiodoBelegradekTheorem
import GroupApproximation.Kazhdan.TorsionFreeHyperbolicKazhdan

/-!
# The Fournier-Facio input paragraph of `thm:torsion-free`

`non_mf_groups_exist.tex`, Section "A torsion-free group with full MF radical",
the paragraph beginning

> Following Fournier-Facio [FFF, §2], let `U` be a universal finitely presented
> torsion-free group, one containing a copy of every finitely presented
> torsion-free group [Chiodo], and let `H₀` be a torsion-free hyperbolic group
> with property (T), obtained from the density model at a parameter between
> `1/3` and `1/2` [Kotowski, Ollivier].

The revised proof uses `F₂` as the third factor and protects the explicit
nonidentity commutator of its two free generators.

Three objects are cited and not proved (`U`, `H₀`, `P`), as are the two
theorems that produce `E`'s acylindrical hyperbolicity and Hull's common
quotient.  Each is stated exactly as the manuscript uses it and collected as a
field of `LiteratureInputs`; **nothing here inhabits that structure**, and every
result downstream of the paragraph carries it as an explicit hypothesis, so the
literature debt is visible in the type.  Everything the paragraph *asserts on
the strength of those citations* is proved here, with no open leaves:

* `kazhdan_of_fournierFacioQuotient` — "Consequently, `P` has property (T)."
* `containsEveryFPTorsionFree_of_fournierFacioQuotient` — `P` inherits `U`'s
  universality along the embedding `U ↪ P`.
* `exists_injective_prodProdWitness` — by universality, `P` contains a subgroup
  `P₁ × P₂ × F₂` with `Pᵢ ≅ P`.  The two closure facts it consumes are
  `ProductFinitePresentation.instProd` (direct products of finitely presented
  groups are finitely presented — proved in this repository, absent from
  Mathlib) and `IsPowerTorsionFree.prod`.
* `E`, the double HNN extension of `P` with stable letters `u₁, u₂` and
  `uᵢ P uᵢ⁻¹ = Pᵢ`, with the two printed conjugation relations, finite
  presentation and torsion-freeness — all in the companion module
  `Manuscript.NonMF.FournierFacioDoubleHNN`.
The protected element is the explicit nonidentity commutator of the two free
generators.  This removes the infinite-simple-group input: the later argument
saturates the normal closure of the image of `[F₂,F₂]` directly.

The paragraph's output, in the form the printed proof of `thm:torsion-free`
consumes it, is `Configuration`; `exists_configuration` assembles one from a
`LiteratureInputs`.

## Acylindrical hyperbolicity

The printed adjective is the parallel hull-saturation lane's class
`Manuscript.NonMF.TorsionFree.IsAcylindricallyHyperbolic`, imported directly:
no placeholder is used here.
-/

namespace GroupApproximation
namespace Manuscript
namespace NonMF
namespace TheoremC

open scoped commutatorElement

/-! ## The literature inputs -/

/-- **The density-model group `H₀`.**  This records the full group used in the
manuscript: it is infinite, finitely presented, torsion-free, hyperbolic, and
has property (T).  Infinitude and hyperbolicity are hypotheses of the cited
small-cancellation construction; omitting them would incorrectly make the
construction apply to the trivial group. -/
abbrev KotowskiOllivierStatement : Prop := Hyperbolic.SharpExistence

/-- **The small-cancellation quotient `P`.**  "Small cancellation over the
relatively hyperbolic pair `(U * H₀, U)` embeds `U` in a finitely presented
torsion-free quotient `P` of `H₀`; torsion-freeness is preserved by Osin's
embedding theorem."  The two clauses used downstream are the surjection
`H₀ ↠ P` and the embedding `U ↪ P`. -/
def FournierFacioQuotientStatement : Prop :=
  ∀ (H₀ U : Type) (_ : Group H₀) (_ : Group U),
    Infinite H₀ → Group.IsFinitelyPresented H₀ →
      IsPowerTorsionFree H₀ → GroupApproximation.Hyperbolic.IsHyperbolicGroup H₀ →
        HasKazhdanPropertyT.{0, 0} H₀ →
          Group.IsFinitelyPresented U → IsPowerTorsionFree U →
            ∃ (P : Type) (_ : Group P),
              Group.IsFinitelyPresented P ∧ IsPowerTorsionFree P ∧
                (∃ p : H₀ →* P, Function.Surjective p) ∧
                (∃ e : U →* P, Function.Injective e)

/-- **Minasyan--Osin's tree criterion.**  "Its Bass--Serre action makes it
acylindrically hyperbolic."  Stated exactly at the manuscript's `E`: the double
HNN extension of `P` along the two `P`-factors of `P₁ × P₂ × W`. -/
def MinasyanOsinStatement : Prop :=
  ∀ (P S : Type) (_ : Group P) (_ : Group S) (f : (P × P × S) →* P)
    (hf : Function.Injective f),
    TorsionFree.IsAcylindricallyHyperbolic (Skeleton f hf)

/-- **Hull's common quotient theorem, Corollary 7.4**, in the form the
manuscript uses it: applied to `E` and `H₀` it gives a surjection `π : E ↠ G₀`
onto a finitely presented torsion-free group with property (T), injective on a
prescribed finite subset of `E`; since `E` is finitely generated, the proof of
that corollary produces `G₀` acylindrically hyperbolic. -/
def HullCommonQuotientStatement : Prop :=
  ∀ (E : Type) (_ : Group E) (H₀ : Type) (_ : Group H₀),
    Group.IsFinitelyPresented E → IsPowerTorsionFree E →
      TorsionFree.IsAcylindricallyHyperbolic E →
      Infinite H₀ → Group.IsFinitelyPresented H₀ →
        IsPowerTorsionFree H₀ → GroupApproximation.Hyperbolic.IsHyperbolicGroup H₀ →
          HasKazhdanPropertyT.{0, 0} H₀ →
            ∀ F : Finset E,
              ∃ (G₀ : Type) (_ : Group G₀) (pi : E →* G₀),
                Function.Surjective pi ∧ Group.IsFinitelyPresented G₀ ∧
                  IsPowerTorsionFree G₀ ∧ HasKazhdanPropertyT.{0, 0} G₀ ∧
                  TorsionFree.IsAcylindricallyHyperbolic G₀ ∧
                    Set.InjOn pi (F : Set E)

/-- **The five statements the Fournier-Facio paragraph cites and does not
prove.**  Nothing in this development inhabits this structure; every result
downstream of the paragraph carries it as an explicit hypothesis, so the
literature debt is visible in the type of each such result. -/
structure LiteratureInputs where
  /-- **Chiodo**, arXiv:1107.1489v4, Theorem 3.10 (= Belegradek, Theorem A.1):
  a finitely presented torsion-free group containing a copy of every finitely
  presented torsion-free group.  This repository already states the sentence,
  as `GroupApproximation.ChiodoBelegradek.Statement`, and proves two of its
  three clauses there. -/
  chiodo : ChiodoBelegradek.Statement
  /-- **Kotowski--Kotowski** and **Ollivier--Wise**: the density model at a
  parameter between `1/3` and `1/2` gives a torsion-free hyperbolic group with
  property (T). -/
  kotowskiOllivier : KotowskiOllivierStatement
  /-- **Fournier-Facio et al., Proposition 2.3** together with **Osin**,
  *Small cancellations over relatively hyperbolic groups and embedding
  theorems*, **Theorem 2.4(5)**: small cancellation over `(U * H₀, U)` embeds
  `U` in a finitely presented torsion-free quotient `P` of `H₀`. -/
  smallCancellationQuotient : FournierFacioQuotientStatement
  /-- **Minasyan--Osin**: acylindrical hyperbolicity of groups acting on trees,
  applied to the Bass--Serre tree of the double HNN extension `E`. -/
  minasyanOsin : MinasyanOsinStatement
  /-- **Hull**, *Small cancellation in acylindrically hyperbolic groups*,
  **Corollary 7.4**: the common quotient theorem. -/
  hullCommonQuotient : HullCommonQuotientStatement

/-! ## What the paragraph proves about `P` -/

/-- **"Consequently, `P` has property (T)."**  `P` is a quotient of `H₀`. -/
theorem kazhdan_of_fournierFacioQuotient {H₀ P : Type} [Group H₀] [Group P]
    (hH₀ : HasKazhdanPropertyT.{0, 0} H₀) (p : H₀ →* P)
    (hp : Function.Surjective p) : HasKazhdanPropertyT.{0, 0} P :=
  HasKazhdanPropertyT.of_surjective p hp hH₀

/-- `P` inherits `U`'s universality along the embedding `U ↪ P`: the "by
universality" of the next printed sentence. -/
theorem containsEveryFPTorsionFree_of_fournierFacioQuotient {U P : Type}
    [Group U] [Group P] (hU : ChiodoBelegradek.ContainsEveryFPTorsionFree U)
    (e : U →* P) (he : Function.Injective e) :
    ChiodoBelegradek.ContainsEveryFPTorsionFree P :=
  hU.comp e he

/-- By universality, `P` contains a subgroup `P₁ × P₂ × W` with `Pᵢ ≅ P`.

The proof is the standard one: `P × P × W` is finitely presented (Mathlib does
not close finite presentation under direct products; this repository does, in
`ProductFinitePresentation.instProd`) and torsion-free
(`IsPowerTorsionFree.prod`), so universality of `P` embeds it in `P`. -/
theorem exists_injective_prodProdWitness {P W : Type} [Group P] [Group W]
    [Group.IsFinitelyPresented P] [Group.IsFinitelyPresented W]
    (hP : IsPowerTorsionFree P) (hW : IsPowerTorsionFree W)
    (huniv : ChiodoBelegradek.ContainsEveryFPTorsionFree P) :
    ∃ f : (P × P × W) →* P, Function.Injective f :=
  huniv.embeds (P × P × W) (hP.prod (hP.prod hW))

/-! ## The output of the paragraph -/

/-- **The state of the construction at the end of the Fournier-Facio
paragraph.**

Every field is a printed sentence of that paragraph, transported through `π`.
`Ambient` is `G₀`; `core` is `π ∘ ι : P → G₀`, whose range is the printed
`Γ = π(P)`; `witness` is the map `F₂ → G₀`; and
`t` is the printed `t = π(u₁)`.

`core_mem_of_witness` is the inclusion of its image in `Γ`;
`t_compresses` is "`tΓt⁻¹ = π(P₁) ≤ Γ`"; and `witness_commute_conj` says the
witness factor commutes with `P₁ = u₁ P u₁⁻¹`, from which `thm:torsion-free`'s
"`J` centralizes `Γ`" is derived. -/
structure Configuration where
  /-- `G₀`, Hull's common quotient. -/
  Ambient : Type
  [groupAmbient : Group Ambient]
  [fpAmbient : Group.IsFinitelyPresented Ambient]
  /-- `G₀` is torsion-free. -/
  torsionFreeAmbient : IsPowerTorsionFree Ambient
  /-- `G₀` has property (T). -/
  kazhdanAmbient : HasKazhdanPropertyT.{0, 0} Ambient
  /-- `G₀` is acylindrically hyperbolic. -/
  acylAmbient : TorsionFree.IsAcylindricallyHyperbolic Ambient
  /-- The finitely presented torsion-free witness group, here `F₂`. -/
  Witness : Type
  [groupWitness : Group Witness]
  /-- The Fournier-Facio base `P`. -/
  Core : Type
  [groupCore : Group Core]
  /-- `P` has property (T). -/
  kazhdanCore : HasKazhdanPropertyT.{0, 0} Core
  /-- `π ∘ ι : P → G₀`; its range is `Γ = π(P)`. -/
  core : Core →* Ambient
  /-- The witness map `F₂ → G₀`. -/
  witness : Witness →* Ambient
  /-- The explicit protected commutator. -/
  distinguished : Witness
  /-- The distinguished element belongs to `[F₂,F₂]`. -/
  distinguished_mem_commutator : distinguished ∈ commutator Witness
  /-- Hull's quotient preserves the distinguished element. -/
  distinguished_image_ne_one : witness distinguished ≠ 1
  /-- The witness image lies in `Γ`. -/
  core_mem_of_witness : ∀ x : Witness, ∃ p : Core, witness x = core p
  /-- `t = π(u₁)`. -/
  t : Ambient
  /-- `t Γ t⁻¹ = π(P₁) ≤ Γ`. -/
  t_compresses : ∀ p : Core, ∃ q : Core, t * core p * t⁻¹ = core q
  /-- The witness factor commutes with `P₁`, transported to the quotient. -/
  witness_commute_conj : ∀ (x : Witness) (p : Core),
    Commute (witness x) (t * core p * t⁻¹)

namespace Configuration

instance instGroupAmbient (C : Configuration) : Group C.Ambient := C.groupAmbient

instance instFPAmbient (C : Configuration) :
    Group.IsFinitelyPresented C.Ambient := C.fpAmbient

instance instGroupWitness (C : Configuration) : Group C.Witness := C.groupWitness

instance instGroupCore (C : Configuration) : Group C.Core := C.groupCore

instance instAcylAmbient (C : Configuration) :
    TorsionFree.IsAcylindricallyHyperbolic C.Ambient := C.acylAmbient

/-- The witness image is nontrivial because it contains the protected
commutator. -/
theorem witnessRange_ne_bot (C : Configuration) : C.witness.range ≠ ⊥ := by
  intro hbot
  apply C.distinguished_image_ne_one
  have hmem : C.witness C.distinguished ∈ C.witness.range :=
    MonoidHom.mem_range.mpr ⟨C.distinguished, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

/-- `G₀` is countable: it is finitely presented. -/
theorem countableAmbient (C : Configuration) : Countable C.Ambient :=
  ChiodoBelegradek.countable_of_isFinitelyPresented C.Ambient

end Configuration

/-! ## Assembling the paragraph -/

/-- **The Fournier-Facio paragraph, assembled.**  Each field of `I` is used
exactly once, and every other step is one of the proofs of this module.  The
literature debt of the whole paragraph is exactly the hypothesis `I`. -/
theorem exists_configuration (I : LiteratureInputs) : Nonempty Configuration := by
  classical
  obtain ⟨U, instU, hUfp, hUtf, hUuniv⟩ := I.chiodo
  obtain ⟨H₀, instH₀, hH₀inf, hH₀fp, hH₀tf, hH₀hyp, hH₀T⟩ :=
    I.kotowskiOllivier
  obtain ⟨P, instP, hPfp, hPtf, ⟨quot, hquot⟩, ⟨emb, hemb⟩⟩ :=
    I.smallCancellationQuotient H₀ U instH₀ instU hH₀inf hH₀fp hH₀tf
      hH₀hyp hH₀T hUfp hUtf
  letI := instU
  letI := instH₀
  letI := instP
  haveI := hPfp
  haveI : Group.IsFinitelyPresented FreeCommutatorWitness :=
    freeCommutatorWitness_finitelyPresented
  let groupFreeCommutatorWitness : Group FreeCommutatorWitness := inferInstance
  -- "Consequently, `P` has property (T)."
  have hPT : HasKazhdanPropertyT.{0, 0} P :=
    kazhdan_of_fournierFacioQuotient hH₀T quot hquot
  -- By universality, `P` contains a subgroup `P₁ × P₂ × F₂`.
  have hPuniv : ChiodoBelegradek.ContainsEveryFPTorsionFree P :=
    containsEveryFPTorsionFree_of_fournierFacioQuotient hUuniv emb hemb
  obtain ⟨f, hf⟩ :=
    exists_injective_prodProdWitness (P := P) (W := FreeCommutatorWitness)
      hPtf freeCommutatorWitness_torsionFree hPuniv
  -- `E`, the double HNN extension, and its three printed properties.
  have hEfp : Group.IsFinitelyPresented (Skeleton f hf) :=
    skeleton_isFinitelyPresented f hf
  have hEtf : IsPowerTorsionFree (Skeleton f hf) := skeleton_torsionFree f hf hPtf
  let groupSkeleton : Group (Skeleton f hf) := inferInstance
  have hEacyl : TorsionFree.IsAcylindricallyHyperbolic (Skeleton f hf) :=
    I.minasyanOsin P FreeCommutatorWitness instP
      groupFreeCommutatorWitness f hf
  let s := freeWitnessCommutator
  obtain ⟨G₀, instG₀, pi, -, hG₀fp, hG₀tf, hG₀T, hG₀acyl, hinj⟩ :=
    I.hullCommonQuotient (Skeleton f hf)
      groupSkeleton H₀ instH₀ hEfp hEtf hEacyl
      hH₀inf hH₀fp hH₀tf hH₀hyp hH₀T
      {1, skeletonIota f hf (factorSimple f s)}
  letI := instG₀
  haveI := hG₀fp
  have hmem1 : (1 : Skeleton f hf) ∈
      ((({1, skeletonIota f hf (factorSimple f s)} : Finset (Skeleton f hf)) :
        Set (Skeleton f hf))) := by simp
  have hmems : skeletonIota f hf (factorSimple f s) ∈
      ((({1, skeletonIota f hf (factorSimple f s)} : Finset (Skeleton f hf)) :
        Set (Skeleton f hf))) := by simp
  -- Hull's injectivity on the protected pair preserves the free commutator.
  have hne : pi (skeletonIota f hf (factorSimple f s)) ≠ 1 := by
    intro hz
    have h1 : pi (skeletonIota f hf (factorSimple f s)) = pi 1 := by
      rw [hz, map_one]
    have h2 := hinj hmems hmem1 h1
    apply freeWitnessCommutator_ne_one
    apply factorSimple_injective f hf
    apply skeletonIota_injective f hf
    rw [h2, map_one, map_one]
  -- The compression relation, transported through `π`.
  have hconj : ∀ p : P, pi (skeletonU₁ f hf) *
      (pi.comp (skeletonIota f hf)) p * (pi (skeletonU₁ f hf))⁻¹
        = (pi.comp (skeletonIota f hf)) (factorOne f p) := by
    intro p
    have h := congrArg pi (skeleton_conj_u₁ f hf p)
    simpa using h
  refine ⟨{
    Ambient := G₀
    torsionFreeAmbient := hG₀tf
    kazhdanAmbient := hG₀T
    acylAmbient := hG₀acyl
    Witness := FreeCommutatorWitness
    Core := P
    kazhdanCore := hPT
    core := pi.comp (skeletonIota f hf)
    witness := (pi.comp (skeletonIota f hf)).comp (factorSimple f)
    distinguished := freeWitnessCommutator
    distinguished_mem_commutator := freeWitnessCommutator_mem_commutator
    distinguished_image_ne_one := hne
    core_mem_of_witness := fun x => ⟨factorSimple f x, rfl⟩
    t := pi (skeletonU₁ f hf)
    t_compresses := fun p => ⟨factorOne f p, hconj p⟩
    witness_commute_conj := ?_ }⟩
  intro x p
  rw [hconj p]
  exact (factorSimple_commute_factorOne f x p).map (pi.comp (skeletonIota f hf))

end TheoremC
end NonMF
end Manuscript
end GroupApproximation
