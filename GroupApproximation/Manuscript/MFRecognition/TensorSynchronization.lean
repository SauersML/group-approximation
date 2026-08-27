import GroupApproximation.Manuscript.MFRecognition.ReducedProductsWiring
import GroupApproximation.Manuscript.MFRecognition.TensorSynchronizationConjugator
import GroupApproximation.Analysis.NonUnitalMFSupportCornerEmbedding
import GroupApproximation.Analysis.UniversalCStarHNN

/-!
# `lem:tensor-sync`: tensor synchronization

This module states and proves the manuscript's Lemma *tensor synchronization*
(`lem:tensor-sync`, `mf_recognition_complexity.tex`):

> Let `Γ` be a countable group with a tracial MF realization `(A_1,ρ_1,τ_1)`,
> let `Q` be a countable group with homomorphisms `β_n : Q → B_n` to finite
> groups such that every `q ≠ 1` satisfies `β_n(q) ≠ 1` for all large `n`, let
> `S ≤ Γ`, and let `τ : S → Q` be a homomorphism.  Suppose that for every `n`
> there is a homomorphism `λ_n : Γ → G_n` to a finite group with
> `ker(λ_n|_S) ≤ ker(β_n ∘ τ)`.  Then there are a separable unital MF
> `C*`-algebra `A`, a homomorphism `V : Γ × Q → U(A)`, a tracial state `T` on
> `A` with `T(V(g,q)) = 0` for `(g,q) ≠ (1,1)`, and a unitary `W ∈ A` with
> `W V(s,1) W* = V(s,τ(s))` for all `s ∈ S`.  Consequently
> `⟨Γ × Q, u | u(s,1)u⁻¹ = (s,τ(s)) (s ∈ S)⟩` admits a tracial MF realization,
> and in particular is MF.

"A separable unital MF `C*`-algebra `A`, a homomorphism `V : Γ × Q → U(A)` and
a tracial state `T` on `A` with `T(V(g,q)) = 0` off the identity" is exactly the
manuscript's *tracial MF realization* of `Γ × Q`, which the repository carries
as `RegularRealizationData` (the tex file marks that identification with
`\leanverified` on `RegularRealizationData.rho_injective` and
`RegularRealizationData.isOperatorMF`).

The last clause is the printed application of `thm:hnn-permanence`:

> For the last assertion, apply Theorem (HNN permanence with a corona
> conjugator) to this realization.  Let `ι` be an injective `*`-homomorphism of
> `A` into a norm matrix corona and put `p = ι(1)`.  The element
> `W̃ = ι(W) + (1−p)` is a unitary of the full corona and implements the
> required covariance on `ι(A)`, so it is the required conjugator.
-/

namespace GroupApproximation
namespace Manuscript
namespace MFRecognition
namespace TensorSynchronization

open Filter PolarLiftingGeneralCStar
open GroupApproximation.Manuscript.OneSidedMFRadical.HNNCoronaConjugatorSentenceAudit
open GroupApproximation.Manuscript.OneSidedMFRadical.TensorSynchronizationAssembly
noncomputable section

/-! ## The inputs of the "Consequently" clause

The "Consequently" clause of `lem:tensor-sync` is an application of
`thm:hnn-permanence`, proved in an earlier section of the manuscript and
formalized by the parallel `hnn-permanence` lane.  Its remaining theorem is
the field of `HNNPermanenceInputs`, and every theorem below that needs it takes a term of
that structure as its leading hypothesis, so the dependency is visible in the
statement of each such theorem.  The corona-embedding step is proved below,
so the structure now contains only the HNN-permanence theorem itself.  This is
the arrangement of
`Manuscript/NonMF/HullSmallCancellation.HullInputs`, and it deliberately keeps
this file independent of the `hnn-permanence` modules while they move: when
that lane lands, one instance of this structure closes every row below.

The headline `manuscriptTensorSynchronization` — the printed conclusion of
`lem:tensor-sync` up to but excluding "Consequently" — needs neither input and
takes no such hypothesis. -/

/-- The remaining theorem consumed by the "Consequently" clause of
`lem:tensor-sync`. -/
structure HNNPermanenceInputs : Prop where
  /-- **`thm:hnn-permanence` (HNN permanence with a corona conjugator)**, in
  the form the printed proof of `lem:tensor-sync` applies it.

  > In the situation of `R = ⟨G, t | tst⁻¹ = θ(s) (s ∈ S)⟩`, suppose that `G`
  > admits a tracial MF realization `(A,ρ,τ)`, and that for some norm matrix
  > corona `𝒬` there are an injective `*`-homomorphism `ι : A → 𝒬` and a
  > unitary `W ∈ 𝒬` with `W ιρ(s) W* = ιρ(θ(s))` for `s ∈ S`.  Then `R` admits
  > a tracial MF realization. -/
  hnnPermanence : ∀ {G : Type} [Group G] [Countable G]
    {S T : Subgroup G} (phi : S ≃* T)
    {A : Type} [CStarAlgebra A] (realization : RegularRealizationData G A)
    {X : ℕ → FiniteModel} [∀ n, Nonempty (X n)]
    (iota : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n)),
    Function.Injective iota →
    ∀ W : unitary (NormMatrixCStarCorona (fun n ↦ X n)),
    (∀ s : S,
      (W : NormMatrixCStarCorona (fun n ↦ X n)) *
            iota ((realization.rho (s : G) : unitary A) : A) *
          star (W : NormMatrixCStarCorona (fun n ↦ X n)) =
        iota ((realization.rho ((phi s : T) : G) : unitary A) : A)) →
    IsRegularlyRealized (HNNExtension G S T phi)

/-- A nonzero unital MF C-star algebra has a faithful unital corona
representation.  The nontriviality hypothesis is necessary: the zero unital
algebra cannot map unitally into a matrix corona.  Every use below obtains it
from the tracial state in a regular realization. -/
theorem unitalCoronaEmbedding :
    ∀ {A : Type} [CStarAlgebra A] [Nontrivial A], IsMFAlgebra A →
      ∃ (X : ℕ → FiniteModel) (hX : ∀ n, Nonempty (X n)),
        letI : ∀ n, Nonempty (X n) := hX
        ∃ iota : A →⋆ₐ[ℂ] NormMatrixCStarCorona (fun n ↦ X n),
          Function.Injective iota := by
  intro A _ _ hA
  rcases hA.2 with ⟨Y, hYne, _hYpos, _hYmono, e, he⟩
  letI : ∀ n, Nonempty (Y n) := hYne
  obtain ⟨X, hXne, E, hE⟩ :=
    NonUnitalMFSupportCornerEmbedding.exists_injective_unital_supportCornerEmbedding
      Y e he
  exact ⟨X, hXne, E, hE⟩

#audit_axioms unitalCoronaEmbedding

/-! ## Applying `thm:hnn-permanence` -/

/-- Conjugating by the image of a unitary is the image of conjugating by that
unitary.

Stated for an abstract target algebra `B` on purpose.  At the norm matrix
corona the `Semiring` and `Algebra` structures are reachable both through
`normMatrixCStarCoronaNormedRing`/`normMatrixCStarCoronaAlgebra` and through
`normMatrixCStarCoronaCStarAlgebra`; the two are definitionally equal but not
syntactically equal, and a `rw` or `simp` that re-elaborates `map_mul` or
`map_star` at the corona picks the second while the goal was built with the
first, so the rewrite reports a missing pattern for a term that is printed in
the goal.  With one `CStarAlgebra B` variable there is no such fork, and the
identity is then applied below with `exact`, which unifies up to instances. -/
theorem unitaryMapOfStarAlgHom_conj {A B : Type*} [CStarAlgebra A]
    [CStarAlgebra B] (f : A →⋆ₐ[ℂ] B) (u : unitary A) (x : A) :
    ((unitaryMapOfStarAlgHom f u : unitary B) : B) * f x *
        star ((unitaryMapOfStarAlgHom f u : unitary B) : B) =
      f ((u : A) * x * star (u : A)) := by
  rw [coe_unitaryMapOfStarAlgHom, map_mul, map_mul, map_star]

/-- **The printed application of `thm:hnn-permanence`.**  "For the last
assertion, apply Theorem (HNN permanence with a corona conjugator) to this
realization, using the faithful unital corona embedding supplied by the MF
realization and the image of `W` as conjugator." -/
theorem isRegularlyRealized_hnn_of_conjugator (hIn : HNNPermanenceInputs)
    {G : Type} [Group G] [Countable G] {S T : Subgroup G} (theta : S ≃* T)
    {A : Type} [CStarAlgebra A] (R : RegularRealizationData G A)
    (W : unitary A)
    (hW : ∀ s : S,
      (W : A) * ((R.rho (s : G) : unitary A) : A) * star (W : A) =
        ((R.rho ((theta s : T) : G) : unitary A) : A)) :
    IsRegularlyRealized (HNNExtension G S T theta) := by
  letI : Nontrivial A := regularRealization_nontrivial R
  obtain ⟨X, hX, iota, hiota⟩ := unitalCoronaEmbedding R.mf
  letI : ∀ n, Nonempty (X n) := hX
  refine hIn.hnnPermanence theta R iota hiota
    (unitaryMapOfStarAlgHom iota W) ?_
  intro s
  -- `exact` unifies up to instances, so the corona's two definitionally equal
  -- `Semiring`/`Algebra` paths cost nothing here; `rw` and `simp` do not, which
  -- is why the algebra of the conjugation is done in
  -- `unitaryMapOfStarAlgHom_conj`, where the target algebra is a variable.
  exact (unitaryMapOfStarAlgHom_conj iota W
    ((R.rho (s : G) : unitary A) : A)).trans (congrArg iota (hW s))

/-! ## The printed edge data of `⟨Γ × Q, u | u(s,1)u⁻¹ = (s,τ(s))⟩` -/

section Edge

variable {Gamma : Type} [Group Gamma]

/-- The subgroup `{(s,1) : s ∈ S}` of `Γ × Q`. -/
def edgeSubgroupSource (S : Subgroup Gamma) (Q : Type) [Group Q] :
    Subgroup (Gamma × Q) :=
  (edgeSource S Q).range

/-- The subgroup `{(s,τ(s)) : s ∈ S}` of `Γ × Q`. -/
def edgeSubgroupTarget {Q : Type} [Group Q] {S : Subgroup Gamma}
    (tau : S →* Q) : Subgroup (Gamma × Q) :=
  (edgeTarget tau).range

/-- Both edge maps are injective on `S`, so they have the same (trivial)
kernel. -/
theorem edgeSource_ker_eq_edgeTarget_ker {Q : Type} [Group Q]
    {S : Subgroup Gamma} (tau : S →* Q) :
    (edgeSource S Q).ker = (edgeTarget tau).ker := by
  ext s
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hs
    have h1 : (S.subtype s) = 1 := congrArg Prod.fst hs
    have hs1 : s = 1 := Subtype.ext h1
    rw [hs1]
    exact map_one _
  · intro hs
    have h1 : (S.subtype s) = 1 := congrArg Prod.fst hs
    have hs1 : s = 1 := Subtype.ext h1
    rw [hs1]
    exact map_one _

/-- `(s,1) ↦ (s,τ(s))`, the edge isomorphism of the printed HNN extension
`⟨Γ × Q, u | u(s,1)u⁻¹ = (s,τ(s)) (s ∈ S)⟩`. -/
def edgeMulEquiv {Q : Type} [Group Q] {S : Subgroup Gamma} (tau : S →* Q) :
    edgeSubgroupSource S Q ≃* edgeSubgroupTarget tau :=
  OneSidedMFRadical.TensorSynchronizationCore.rangeMulEquivOfKerEq
    (edgeSource S Q) (edgeTarget tau) (edgeSource_ker_eq_edgeTarget_ker tau)

end Edge

/-! ## Kernels through the range restriction -/

/-- The range restriction of a homomorphism has the same kernel as the
homomorphism itself, after composition with an arbitrary source map. -/
theorem ker_rangeRestrict_comp {H K L : Type} [Group H] [Group K] [Group L]
    (f : H →* K) (g : L →* H) :
    (f.rangeRestrict.comp g).ker = (f.comp g).ker := by
  ext x
  simp only [MonoidHom.mem_ker]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-! ## The generated algebra `A = C*(V(Γ × Q), W)` -/

section Generated

variable {Gamma : Type} [Group Gamma] [Countable Gamma]
  {Q : Type} [Group Q] [Countable Q]
  {A1 : Type} [CStarAlgebra A1]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **"Let `A` be the `C*`-algebra generated by `V(Γ × Q)` and `W`; it is
separable and unital, and MF by Lemma (reduced products of MF algebras).  The
triple `(A, V, T|_A)` is a tracial MF realization of `Γ × Q`."**

Together with the last sentence of the second printed paragraph
(`W V(s,1) W* = V(s,τ(s))`), this is the whole conclusion of `lem:tensor-sync`
before the "Consequently" clause.  The finite groups `E_n` and the coordinate
maps `ell n` are the abstract interface of `TensorSynchronizationData`.

The budgets above and the instance block that opens the proof are elaboration
cost, not mathematics.  The C-star structure of `CStarMatrix (E n) (E n) A_1`
is built from the spectral order of `A_1`, so the search for it re-derives
`PartialOrder A_1` and `StarOrderedRing A_1` at every one of the many
occurrences of the reduced product below; supplying those two once, and then
the coordinate C-star instance itself, turns that search into a lookup.  They
are introduced with `letI` rather than `haveI` so that they stay transparent
and the coordinate algebras keep the same instances the landed
`TensorSynchronizationData` declarations were elaborated with. -/
theorem exists_syncRealization (R1 : RegularRealizationData Gamma A1)
    {S : Subgroup Gamma} (tau : S →* Q)
    (E : ℕ → Type) [∀ n, Group (E n)] [∀ n, Fintype (E n)]
    [∀ n, DecidableEq (E n)]
    (ell : ∀ n, Gamma × Q →* E n)
    (hdetect : ∀ z : Gamma × Q, z.1 = 1 → z.2 ≠ 1 →
      ∀ᶠ n in cofinite, ell n z ≠ 1)
    (hker : ∀ n, ((ell n).comp (edgeSource S Q)).ker =
      ((ell n).comp (edgeTarget tau)).ker) :
    ∃ (A : Type) (inst : CStarAlgebra A),
      letI : CStarAlgebra A := inst
      ∃ D : RegularRealizationData (Gamma × Q) A, ∃ W : unitary A, ∀ s : S,
        (W : A) * ((D.rho (edgeSource S Q s) : unitary A) : A) *
            star (W : A) =
          ((D.rho (edgeTarget tau s) : unitary A) : A) := by
  letI : ∀ n, Nonempty (E n) := fun n ↦ coordNonempty E n
  letI : PartialOrder A1 := CStarAlgebra.spectralOrder A1
  letI : StarOrderedRing A1 := CStarAlgebra.spectralOrderedRing A1
  letI : ∀ n, CStarAlgebra (CStarMatrix (E n) (E n) A1) := fun n ↦ inferInstance
  haveI : Nontrivial A1 := nontrivial_of_tracialState R1.tau
  haveI : ∀ n, Nontrivial (CStarMatrix (E n) (E n) A1) := fun n ↦
    coordAlgebra_nontrivial E R1.tau n
  haveI : Countable (Multiplicative ℤ) :=
    Countable.of_equiv ℤ Multiplicative.ofAdd
  haveI : Countable (Monoid.Coprod (Gamma × Q) (Multiplicative ℤ)) :=
    Monoid.Coprod.mk_surjective.countable
  obtain ⟨W0, hW0⟩ := exists_syncConjugator E tau R1 ell hker
  set Phi : Monoid.Coprod (Gamma × Q) (Multiplicative ℤ) →*
      unitary (CStarProductCorona
        (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite) :=
    representedGroupWithUnitaryHom (syncRep E R1 ell) W0 with hPhidef
  haveI : TopologicalSpace.SeparableSpace ↥(groupGeneratedCStar Phi) :=
    groupGeneratedCStar_separableSpace Phi
  -- "`B'_n = A_1 ⊗ M_{k_n}(ℂ)`, which is MF by Lemma (reduced products of MF
  -- algebras)."
  have hBMF : ∀ n, IsMFAlgebra (CStarMatrix (E n) (E n) A1) := fun n ↦
    isMFAlgebra_cstarMatrix_fintype R1.mf
  have hAMF : IsMFAlgebra ↥(groupGeneratedCStar Phi) :=
    reducedProduct_separableSubalgebra_isMF
      (fun n ↦ CStarMatrix (E n) (E n) A1) hBMF ↥(groupGeneratedCStar Phi)
      (groupGeneratedCStar Phi).subtype.toNonUnitalStarAlgHom
      (fun x y hxy ↦ Subtype.ext hxy)
  -- `V` and `W` are the two generators of `A = C*(V(Γ × Q), W)`, so they are
  -- the values of `Phi` on the two injections of the free product.  `simp`
  -- unfolds `representedGroupWithUnitaryHom` to `Monoid.Coprod.lift` and then
  -- stops, so the two universal-property equations are named outright.
  have hVeq : ∀ z : Gamma × Q,
      Phi (Monoid.Coprod.inl z) = syncRep E R1 ell z := by
    intro z
    rw [hPhidef]
    exact Monoid.Coprod.lift_apply_inl _ _ z
  have hWeq : Phi (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))) = W0 := by
    rw [hPhidef]
    refine (Monoid.Coprod.lift_apply_inr _ _ _).trans ?_
    show W0 ^ (1 : ℤ) = W0
    exact zpow_one W0
  refine ⟨↥(groupGeneratedCStar Phi), inferInstance,
    ⟨hAMF, (groupGeneratedUnitaryHom Phi).comp Monoid.Coprod.inl,
      groupGeneratedTrace Phi (syncTrace E R1.tau), ?_⟩,
    groupGeneratedUnitaryHom Phi
      (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))), ?_⟩
  · intro z hz
    show syncTrace E R1.tau
        ((Phi (Monoid.Coprod.inl z) :
          unitary (CStarProductCorona
            (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite)) :
          CStarProductCorona (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite)
      = 0
    rw [hVeq z]
    exact syncTrace_syncRep_eq_zero E R1 ell hdetect z hz
  · intro s
    apply Subtype.ext
    show ((Phi (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))) :
          unitary (CStarProductCorona
            (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite)) :
          CStarProductCorona (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite) *
        ((Phi (Monoid.Coprod.inl (edgeSource S Q s)) :
          unitary (CStarProductCorona
            (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite)) :
          CStarProductCorona (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite) *
        star ((Phi (Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ℤ))) :
          unitary (CStarProductCorona
            (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite)) :
          CStarProductCorona (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite)
      = ((Phi (Monoid.Coprod.inl (edgeTarget tau s)) :
          unitary (CStarProductCorona
            (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite)) :
          CStarProductCorona (fun n ↦ CStarMatrix (E n) (E n) A1) cofinite)
    rw [hWeq, hVeq, hVeq]
    exact hW0 s

end Generated

/-! ## The printed statement -/

section Manuscript

variable {Gamma : Type} [Group Gamma] [Countable Gamma]
  {Q : Type} [Group Q] [Countable Q]
  {A1 : Type} [CStarAlgebra A1]

/-- **`lem:tensor-sync` (tensor synchronization).**

"Let `Γ` be a countable group with a tracial MF realization `(A_1,ρ_1,τ_1)`,
let `Q` be a countable group with homomorphisms `β_n : Q → B_n` to finite
groups such that every `q ≠ 1` satisfies `β_n(q) ≠ 1` for all large `n`, let
`S ≤ Γ`, and let `τ : S → Q` be a homomorphism.  Suppose that for every `n`
there is a homomorphism `λ_n : Γ → G_n` to a finite group with
`ker(λ_n|_S) ≤ ker(β_n ∘ τ)`.  Then there are a separable unital MF
`C*`-algebra `A`, a homomorphism `V : Γ × Q → U(A)`, a tracial state `T` on `A`
with `T(V(g,q)) = 0` for `(g,q) ≠ (1,1)`, and a unitary `W ∈ A` with
`W V(s,1) W* = V(s,τ(s))` for all `s ∈ S`." -/
theorem manuscriptTensorSynchronization
    (R1 : RegularRealizationData Gamma A1)
    {Bfin : ℕ → Type} [∀ n, Group (Bfin n)] [∀ n, Fintype (Bfin n)]
    (bet : ∀ n, Q →* Bfin n)
    (hbet : ∀ q : Q, q ≠ 1 → ∀ᶠ n in atTop, bet n q ≠ 1)
    {S : Subgroup Gamma} (tau : S →* Q)
    {Gfin : ℕ → Type} [∀ n, Group (Gfin n)] [∀ n, Fintype (Gfin n)]
    (lam : ∀ n, Gamma →* Gfin n)
    (hlam : ∀ n, ((lam n).comp S.subtype).ker ≤ ((bet n).comp tau).ker) :
    ∃ (A : Type) (inst : CStarAlgebra A),
      letI : CStarAlgebra A := inst
      ∃ D : RegularRealizationData (Gamma × Q) A, ∃ W : unitary A, ∀ s : S,
        (W : A) * ((D.rho (edgeSource S Q s) : unitary A) : A) *
            star (W : A) =
          ((D.rho (edgeTarget tau s) : unitary A) : A) := by
  classical
  -- `E_n` is the image of `(λ_n, β_n) : Γ × Q → G_n × B_n`.
  letI : ∀ n, Fintype ↥((pairHom (lam n) (bet n)).range) := fun n ↦
    Fintype.ofFinite _
  letI : ∀ n, DecidableEq ↥((pairHom (lam n) (bet n)).range) := fun n ↦
    Classical.decEq _
  refine exists_syncRealization R1 tau
    (fun n ↦ ↥((pairHom (lam n) (bet n)).range))
    (fun n ↦ (pairHom (lam n) (bet n)).rangeRestrict) ?_ ?_
  · intro z _ hz2
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [hbet z.2 hz2] with n hn
    intro hcon
    apply hn
    have hval : (pairHom (lam n) (bet n)) z = 1 := congrArg Subtype.val hcon
    exact congrArg Prod.snd hval
  · intro n
    rw [ker_rangeRestrict_comp, ker_rangeRestrict_comp]
    exact pairHom_edgeKer_eq tau (lam n) (bet n) (hlam n)

/-- **The "Consequently" clause of `lem:tensor-sync`.**  "Consequently
`⟨Γ × Q, u | u(s,1)u⁻¹ = (s,τ(s)) (s ∈ S)⟩` admits a tracial MF realization,
and in particular is MF." -/
theorem manuscriptTensorSynchronization_hnn (hIn : HNNPermanenceInputs)
    (R1 : RegularRealizationData Gamma A1)
    {Bfin : ℕ → Type} [∀ n, Group (Bfin n)] [∀ n, Fintype (Bfin n)]
    (bet : ∀ n, Q →* Bfin n)
    (hbet : ∀ q : Q, q ≠ 1 → ∀ᶠ n in atTop, bet n q ≠ 1)
    {S : Subgroup Gamma} (tau : S →* Q)
    {Gfin : ℕ → Type} [∀ n, Group (Gfin n)] [∀ n, Fintype (Gfin n)]
    (lam : ∀ n, Gamma →* Gfin n)
    (hlam : ∀ n, ((lam n).comp S.subtype).ker ≤ ((bet n).comp tau).ker) :
    IsRegularlyRealized
      (HNNExtension (Gamma × Q) (edgeSubgroupSource S Q)
        (edgeSubgroupTarget tau) (edgeMulEquiv tau)) := by
  obtain ⟨A, inst, D, W, hW⟩ :=
    manuscriptTensorSynchronization R1 bet hbet tau lam hlam
  letI : CStarAlgebra A := inst
  refine isRegularlyRealized_hnn_of_conjugator hIn (edgeMulEquiv tau) D W ?_
  intro s
  obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp s.2
  have hst : (edgeSource S Q).rangeRestrict t = s := Subtype.ext ht
  have hth : ((edgeMulEquiv tau s : edgeSubgroupTarget tau) : Gamma × Q)
      = edgeTarget tau t := by
    rw [← hst]
    exact congrArg Subtype.val
      (OneSidedMFRadical.TensorSynchronizationCore.rangeMulEquivOfKerEq_rangeRestrict
        (edgeSource S Q) (edgeTarget tau)
        (edgeSource_ker_eq_edgeTarget_ker tau) t)
  rw [hth, ← ht]
  exact hW t

/-- **"In particular, `⟨Γ × Q, u | u(s,1)u⁻¹ = (s,τ(s))⟩` is MF."**

Countability of the HNN extension is the one side condition the printed
sentence leaves implicit; it is carried here as a hypothesis rather than
guessed. -/
theorem manuscriptTensorSynchronization_isOperatorMF (hIn : HNNPermanenceInputs)
    (R1 : RegularRealizationData Gamma A1)
    {Bfin : ℕ → Type} [∀ n, Group (Bfin n)] [∀ n, Fintype (Bfin n)]
    (bet : ∀ n, Q →* Bfin n)
    (hbet : ∀ q : Q, q ≠ 1 → ∀ᶠ n in atTop, bet n q ≠ 1)
    {S : Subgroup Gamma} (tau : S →* Q)
    {Gfin : ℕ → Type} [∀ n, Group (Gfin n)] [∀ n, Fintype (Gfin n)]
    (lam : ∀ n, Gamma →* Gfin n)
    (hlam : ∀ n, ((lam n).comp S.subtype).ker ≤ ((bet n).comp tau).ker)
    (hcount : Countable (HNNExtension (Gamma × Q) (edgeSubgroupSource S Q)
      (edgeSubgroupTarget tau) (edgeMulEquiv tau))) :
    IsOperatorMF
      (HNNExtension (Gamma × Q) (edgeSubgroupSource S Q)
        (edgeSubgroupTarget tau) (edgeMulEquiv tau)) := by
  haveI := hcount
  exact isOperatorMF_of_isRegularlyRealized
    (manuscriptTensorSynchronization_hnn hIn R1 bet hbet tau lam hlam)

end Manuscript

end

end TensorSynchronization
end MFRecognition
end Manuscript
end GroupApproximation
