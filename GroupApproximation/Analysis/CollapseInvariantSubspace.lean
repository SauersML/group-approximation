import GroupApproximation.Analysis.CollapseLambdaCocycle
import GroupApproximation.Analysis.OmegaHilbertComplete
import GroupApproximation.Analysis.ProjectionOrbitCollapse

/-!
# `K_q = closure Λ(𝓘_q)`, and the printed paragraph inside it

Proof-ledger rows `CO.21` and `CO.21b`, the paragraph *An exact cocycle* and
the last paragraph of the proof of `thm:projection-collapse` in
`non_mf_groups_exist.tex` (navigate by the label; that file is under
concurrent edit).

The printed proof names a space and works inside it:

> `Λ` extends to the closed invariant subspace `K_q = closure Λ(𝓘_q)` of
> `K_ω`, on which `π(h) Λ(z) = Λ(Θ(h) z Θ(h)*)`; `β(g) = Λ(d_g)` is a
> `1`-cocycle for `π` on `K_q`, and Delorme–Guichardet applies to it.

`Analysis/CollapseLambdaCocycle` proved the equivariance and the cocycle
identity, and recorded that it formed no closure, because the identity holds
on the ideal itself and every use of it is at an element of the ideal.  That
divergence from the printed wording is what this file removes: `K_q` is
formed, it is closed, it is invariant, `β` lands in it, and the endpoint runs
there rather than on all of `K_ω`.

## What each piece is

* `Kq` is the printed `closure Λ(𝓘_q)`: the topological closure of the range
  of the linear map `Λ` of `Analysis/RankNormalizedLambda`.  `mem_Kq_iff` says
  so; nothing else about it is used.
* `isClosed_Kq` and `completeSpace_Kq` are the two words *closed* and
  (through `Analysis/OmegaHilbertComplete`) *Hilbert*: a closed subspace of a
  complete space is complete, which is the hypothesis Delorme–Guichardet
  needs.
* `conjIsometryEquiv_mem_Kq` is the printed *invariant*.  Its content is
  `CollapseLambdaCocycle.conjIsometryEquiv_lambda` together with two-sidedness
  of the ideal: conjugation carries `Λ(𝓘_q)` into itself, and a continuous map
  carries the closure of a set into the closure of its image.  No estimate is
  involved, and none is available — the equivariance is exact on the ideal and
  the closure is taken afterwards, which is the order the print takes them in.
* `restrictUnitary` is the restriction of a unitary representation to an
  invariant subspace.  `Kazhdan/KazhdanFixedSpace.restrictToInvariantSubspace`
  is the same construction for a real orthogonal representation; the collapse
  consumes Delorme–Guichardet in its complex form, so it needs the complex
  one.  The inverse is induced by `g⁻¹`, which is what makes the restriction
  an isometric *equivalence* of `K_q` rather than an endomorphism of it.
* `betaKq` is `β(g) = Λ(d_g)` as a map into `K_q`, and `betaKq_cocycle` is
  `eq:collapse-cocycle` read there.
* `collapse_contradiction_Kq` is the printed last paragraph, run on `K_q`.

## The objects are the printed ones

`ProjectionOrbitCollapse.sub_conj_mul` proves `eq:collapse-cocycle` in an
arbitrary ring with involution, and `CO.21` has recorded that as the reason
its objects are substituted rather than literal.  `printedDisplacement` and
`printedDisplacement_cocycle` are that identity at the printed objects: the
displacements `d_g = Θ(g) p Θ(g)* − p` of an actual corona representation,
`Θ` being the one a coordinatewise unitary lift induces through
`unitarySequenceToCorona`.  `printed_betaKq_cocycle` is then the printed
sentence with nothing substituted — the printed displacement family, the
printed `Λ`, the printed space `K_q`, and the printed representation `π`
restricted to it.

## What is still a binder, and why

`collapse_contradiction_Kq` takes `htransport` — the identification of
`Fix π(sLs⁻¹)` with `Fix π(L)` — rather than deriving it, and at this
generality there is nothing to derive it from.  The derivation is
`Analysis/CollapseTransportEndpoint.transport_corona`, which needs a
`KazhdanCompressionRep` bundle, and
`Analysis/CollapseDelormeCorona.collapse_contradiction_corona_delorme`
discharges it for that bundle — in the ambient `K_ω`.  Its `K_q` counterpart
wants the fixed-space comparison read inside the subspace, and is not built
here.

The other thing this file does not do is choose the lift: `Θ` enters as a
coordinatewise unitary family, which is `lem:unitarycorona`'s output and is
supplied by `Analysis/CollapseUnitaryLift` on the badged route.  Nor does it
move the badged route: `Sofic/ProjectionCompressionCollapse` still reaches its
contradiction through `Analysis/CollapsePrintedContradiction`, which works in
`K_ω`.
-/

namespace GroupApproximation
namespace CollapseInvariantSubspace

open Filter Matrix Topology
open UltraproductModelConstruction RankNormalizedHilbertization
open KOmegaHilbert CollapseCocycleAnalytic CollapseUltraproductRepresentation
open RankNormalizedLambda CollapseLambdaCocycle
open scoped Matrix.Norms.L2Operator

noncomputable section

universe u v

/-! ## A unitary representation restricted to an invariant subspace -/

section Restrict

variable {G : Type u} [Group G] {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Restriction of a unitary representation to an invariant subspace.**

The real case is `Kazhdan/KazhdanFixedSpace.restrictToInvariantSubspace`; this
is the same construction over `ℂ`, which is the field the collapse's
Delorme–Guichardet step works over.  Surjectivity of the restricted map is
what makes the value an isometric equivalence of `U` rather than an isometry
of `U` into itself, and it comes from `g⁻¹`, which preserves `U` by the same
hypothesis. -/
def restrictUnitary (π : G →* (E ≃ₗᵢ[ℂ] E)) (U : Submodule ℂ E)
    (hU : ∀ g : G, ∀ x ∈ U, π g x ∈ U) : G →* (U ≃ₗᵢ[ℂ] U) where
  toFun g :=
    LinearIsometryEquiv.ofSurjective
      { toLinearMap :=
          { toFun := fun x ↦ ⟨π g x.1, hU g x.1 x.2⟩
            map_add' := fun x y ↦ by ext; simp
            map_smul' := fun r x ↦ by ext; simp }
        norm_map' := fun x ↦ (π g).norm_map x.1 }
      (by
        intro y
        refine ⟨⟨π g⁻¹ y.1, hU g⁻¹ y.1 y.2⟩, ?_⟩
        ext
        simp)
  map_one' := by
    ext x
    simp
  map_mul' := by
    intro g h
    ext x
    simp [map_mul]

@[simp] theorem coe_restrictUnitary (π : G →* (E ≃ₗᵢ[ℂ] E)) (U : Submodule ℂ E)
    (hU : ∀ g : G, ∀ x ∈ U, π g x ∈ U) (g : G) (x : U) :
    (restrictUnitary π U hU g x : E) = π g x.1 := rfl

end Restrict

/-! ## `K_q` -/

section Space

variable (Y : ℕ → FiniteModel) [∀ n, Nonempty (Y n)]

/-- **The printed `K_q = closure Λ(𝓘_q)`.**  The closure of the range of `Λ`,
which is the closure of the image of the printed ideal because `Λ` is defined
on the ideal and nowhere else. -/
def Kq (P : MatFam Y) (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ) ≤ cofinite) :
    Submodule ℂ (KRank Y P ω) :=
  (LinearMap.range (lambda Y P ω hω)).topologicalClosure

/-- Membership in `K_q` is membership in the closure of `Λ(𝓘_q)`; this is the
only fact about `K_q` the file uses. -/
theorem mem_Kq_iff (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (x : KRank Y P ω) :
    x ∈ Kq Y P ω hω ↔
      x ∈ closure ((LinearMap.range (lambda Y P ω hω)) : Set (KRank Y P ω)) :=
  Iff.rfl

/-- `Λ` takes the printed ideal into `K_q`. -/
theorem lambda_mem_Kq (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (z : rankIdeal Y P) :
    lambda Y P ω hω z ∈ Kq Y P ω hω := by
  rw [mem_Kq_iff]
  exact subset_closure (LinearMap.mem_range_self (lambda Y P ω hω) z)

/-- **`K_q` is closed**, which is the printed adjective and not a lemma: it is
a closure. -/
theorem isClosed_Kq (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) :
    IsClosed (Kq Y P ω hω : Set (KRank Y P ω)) := by
  show IsClosed (closure ((LinearMap.range (lambda Y P ω hω)) :
    Set (KRank Y P ω)))
  exact isClosed_closure

/-- **`K_q` is a Hilbert space.**  A closed subspace of the complete `K_ω` of
`Analysis/OmegaHilbertComplete`; this is the completeness hypothesis
Delorme–Guichardet consumes. -/
instance completeSpace_Kq (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) : CompleteSpace (Kq Y P ω hω) :=
  (isClosed_Kq Y P ω hω).completeSpace_coe

/-- **`K_q` is invariant.**  Conjugation by a coordinatewise unitary family
carries `Λ(𝓘_q)` into itself — that is `conjIsometryEquiv_lambda` together
with two-sidedness of the ideal — and a continuous map carries the closure of
a set into the closure of its image. -/
theorem conjIsometryEquiv_mem_Kq (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite)
    (U : ∀ n, Matrix.unitaryGroup (Y n) ℂ) (x : KRank Y P ω)
    (hx : x ∈ Kq Y P ω hω) :
    conjIsometryEquiv Y (rankWeight Y P) ω (rankWeight_nonneg Y P) U x
      ∈ Kq Y P ω hω := by
  have hmaps :
      (conjIsometryEquiv Y (rankWeight Y P) ω (rankWeight_nonneg Y P) U) ''
          ((LinearMap.range (lambda Y P ω hω)) : Set (KRank Y P ω))
        ⊆ ((LinearMap.range (lambda Y P ω hω)) : Set (KRank Y P ω)) := by
    rintro _ ⟨u, hu, rfl⟩
    have hu' : ∃ z : rankIdeal Y P, lambda Y P ω hω z = u := hu
    obtain ⟨z, rfl⟩ := hu'
    have hmem : coronaLinear Y (unitarySequenceBounded Y U) *
        (z : NormMatrixCStarCorona (fun n ↦ Y n)) *
        star (coronaLinear Y (unitarySequenceBounded Y U))
        ∈ rankIdeal Y P :=
      mul_mem_rankIdeal Y P _ _ z.2
    have hval :
        conjIsometryEquiv Y (rankWeight Y P) ω (rankWeight_nonneg Y P) U
            (lambda Y P ω hω z)
          = lambda Y P ω hω ⟨_, hmem⟩ :=
      conjIsometryEquiv_lambda Y P ω hω U z ⟨_, hmem⟩ rfl
    have hrange : lambda Y P ω hω (⟨_, hmem⟩ : rankIdeal Y P)
        ∈ ((LinearMap.range (lambda Y P ω hω)) : Set (KRank Y P ω)) :=
      LinearMap.mem_range_self (lambda Y P ω hω) ⟨_, hmem⟩
    rw [hval]
    exact hrange
  have hxc : x ∈ closure ((LinearMap.range (lambda Y P ω hω)) :
      Set (KRank Y P ω)) := hx
  have himg :
      conjIsometryEquiv Y (rankWeight Y P) ω (rankWeight_nonneg Y P) U x
        ∈ closure
            ((conjIsometryEquiv Y (rankWeight Y P) ω
                (rankWeight_nonneg Y P) U) ''
              ((LinearMap.range (lambda Y P ω hω)) : Set (KRank Y P ω))) :=
    image_closure_subset_closure_image
      (conjIsometryEquiv Y (rankWeight Y P) ω
        (rankWeight_nonneg Y P) U).continuous
      (Set.mem_image_of_mem _ hxc)
  exact closure_mono hmaps himg

section Rep

variable {H : Type u} [Group H]

/-- **`K_q` is invariant under `π`**, which is the printed word. -/
theorem conjRep_mem_Kq (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite)
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ)) (g : H)
    (x : KRank Y P ω) (hx : x ∈ Kq Y P ω hω) :
    conjRep Y (rankWeight Y P) ω (rankWeight_nonneg Y P) Θ g x
      ∈ Kq Y P ω hω :=
  conjIsometryEquiv_mem_Kq Y P ω hω (fun n ↦ Θ g n) x hx

/-- **`π` on `K_q`.**  The printed *"`π` is a unitary representation of `H` on
the closed invariant subspace `K_q`"*. -/
def conjRepKq (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite)
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ)) :
    H →* (Kq Y P ω hω ≃ₗᵢ[ℂ] Kq Y P ω hω) :=
  restrictUnitary (conjRep Y (rankWeight Y P) ω (rankWeight_nonneg Y P) Θ)
    (Kq Y P ω hω) fun g x hx ↦ conjRep_mem_Kq Y P ω hω Θ g x hx

@[simp] theorem coe_conjRepKq (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite)
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ)) (g : H)
    (x : Kq Y P ω hω) :
    ((conjRepKq Y P ω hω Θ g x : Kq Y P ω hω) : KRank Y P ω)
      = conjRep Y (rankWeight Y P) ω (rankWeight_nonneg Y P) Θ g
          (x : KRank Y P ω) := rfl

/-! ## `β` in `K_q` -/

/-- **`β(g) = Λ(d_g)`, valued in `K_q`.** -/
def betaKq (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (d : H → rankIdeal Y P) (g : H) :
    Kq Y P ω hω :=
  ⟨lambda Y P ω hω (d g), lambda_mem_Kq Y P ω hω (d g)⟩

omit [Group H] in
@[simp] theorem coe_betaKq (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (d : H → rankIdeal Y P) (g : H) :
    ((betaKq Y P ω hω d g : Kq Y P ω hω) : KRank Y P ω)
      = lambda Y P ω hω (d g) := rfl

omit [Group H] in
/-- `β` vanishes in `K_q` exactly when `Λ(d_g)` vanishes in `K_ω`: the
inclusion is injective, so the nonvanishing of the previous printed step is
the nonvanishing needed here. -/
theorem betaKq_eq_zero_iff (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (d : H → rankIdeal Y P) (g : H) :
    betaKq Y P ω hω d g = 0 ↔ lambda Y P ω hω (d g) = 0 := by
  constructor
  · intro h
    exact congrArg (fun y : Kq Y P ω hω ↦ (y : KRank Y P ω)) h
  · intro h
    exact Subtype.ext h

/-- **`CO.21` in the printed space.**  The cocycle identity for `β` as a map
into `K_q`, for `π` restricted to `K_q`.  Its content is
`CollapseLambdaCocycle.lambda_cocycle`; what is new is that both sides live in
the printed subspace, so the equation is the printed one and not its image in
the ambient `K_ω`. -/
theorem betaKq_cocycle (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite)
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ)) (d : H → rankIdeal Y P)
    (hd : ∀ g h : H, (d (g * h) : NormMatrixCStarCorona (fun n ↦ Y n))
      = (d g : NormMatrixCStarCorona (fun n ↦ Y n))
        + coronaLinear Y (unitarySequenceBounded Y (Θ g)) *
            (d h : NormMatrixCStarCorona (fun n ↦ Y n)) *
            star (coronaLinear Y (unitarySequenceBounded Y (Θ g))))
    (g h : H) :
    betaKq Y P ω hω d (g * h)
      = betaKq Y P ω hω d g
        + conjRepKq Y P ω hω Θ g (betaKq Y P ω hω d h) := by
  refine Subtype.ext ?_
  show lambda Y P ω hω (d (g * h))
    = lambda Y P ω hω (d g)
      + conjRep Y (rankWeight Y P) ω (rankWeight_nonneg Y P) Θ g
          (lambda Y P ω hω (d h))
  exact lambda_cocycle Y P ω hω Θ d hd g h

/-! ## The printed last paragraph, on `K_q` -/

/-- **`CO.21b` on `K_q`.**  The printed contradiction, run on the printed
closed invariant subspace rather than on the ambient `K_ω`:
Delorme–Guichardet applies because `K_q` is a complex Hilbert space
(`completeSpace_Kq`), `π` acts on it by isometries (`conjRepKq`), and `β`
takes its values there (`betaKq`).

`hcompressed` is the printed `d_{sas⁻¹} = 0` read through `Λ`, and `hne` is
the nonvanishing of the previous printed step.  `htransport` is the
fixed-space identification, and it is a hypothesis here because the group and
the compression enter as bare data: the derivation of it is
`Analysis/CollapseTransportEndpoint.transport_corona`, which needs a
`KazhdanCompressionRep` bundle, and the module docstring records what its
`K_q` counterpart would take. -/
theorem collapse_contradiction_Kq (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (hT : HasKazhdanPropertyT.{u, u} H)
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ)) (d : H → rankIdeal Y P)
    (c : H → H)
    (hd : ∀ g h : H, (d (g * h) : NormMatrixCStarCorona (fun n ↦ Y n))
      = (d g : NormMatrixCStarCorona (fun n ↦ Y n))
        + coronaLinear Y (unitarySequenceBounded Y (Θ g)) *
            (d h : NormMatrixCStarCorona (fun n ↦ Y n)) *
            star (coronaLinear Y (unitarySequenceBounded Y (Θ g))))
    (hcompressed : ∀ a : H, lambda Y P ω hω (d (c a)) = 0)
    (htransport : ∀ y : Kq Y P ω hω,
      (∀ a : H, conjRepKq Y P ω hω Θ (c a) y = y) →
        ∀ g : H, conjRepKq Y P ω hω Θ g y = y)
    (hne : ∃ g : H, lambda Y P ω hω (d g) ≠ 0) : False := by
  obtain ⟨g₀, hg₀⟩ := hne
  refine CollapseDelormeEndpoint.collapse_contradiction_of_hasKazhdanPropertyT
    hT (conjRepKq Y P ω hω Θ) (betaKq Y P ω hω d) c
    (betaKq_cocycle Y P ω hω Θ d hd)
    (fun a ↦ (betaKq_eq_zero_iff Y P ω hω d (c a)).2 (hcompressed a))
    htransport ⟨g₀, ?_⟩
  intro hzero
  exact hg₀ ((betaKq_eq_zero_iff Y P ω hω d g₀).1 hzero)

/-! ## The printed objects -/

/-- **The corona representation of a coordinatewise unitary lift.**  The
printed `Θ(g) = [U_n(g)]`, as a homomorphism into the unitaries of the
corona. -/
def coronaRepOfLift (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ)) :
    H →* unitary (NormMatrixCStarCorona (fun n ↦ Y n)) :=
  (unitarySequenceToCorona Y).comp Θ

@[simp] theorem coe_coronaRepOfLift
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ)) (g : H) :
    ((coronaRepOfLift Y Θ g : unitary (NormMatrixCStarCorona (fun n ↦ Y n))) :
        NormMatrixCStarCorona (fun n ↦ Y n))
      = coronaLinear Y (unitarySequenceBounded Y (Θ g)) := rfl

/-- **The printed displacement `d_g = Θ(g) p Θ(g)* − p`**, as an element of
the printed ideal.  `hmem` is the printed *"`𝓘_q` is inner invariant, so
`d_g ∈ 𝓘_q` for every `g ∈ L`"*, which
`Analysis/CollapseDisplacementIdeal.displacement_mem_rankIdeal` proves. -/
def printedDisplacement (P : MatFam Y)
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ))
    (p : NormMatrixCStarCorona (fun n ↦ Y n))
    (hmem : ∀ g : H,
      ProjectionOrbitCollapse.conj (coronaRepOfLift Y Θ) p g - p
        ∈ rankIdeal Y P) (g : H) : rankIdeal Y P :=
  ⟨ProjectionOrbitCollapse.conj (coronaRepOfLift Y Θ) p g - p, hmem g⟩

@[simp] theorem coe_printedDisplacement (P : MatFam Y)
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ))
    (p : NormMatrixCStarCorona (fun n ↦ Y n))
    (hmem : ∀ g : H,
      ProjectionOrbitCollapse.conj (coronaRepOfLift Y Θ) p g - p
        ∈ rankIdeal Y P) (g : H) :
    ((printedDisplacement Y P Θ p hmem g : rankIdeal Y P) :
        NormMatrixCStarCorona (fun n ↦ Y n))
      = ProjectionOrbitCollapse.conj (coronaRepOfLift Y Θ) p g - p := rfl

/-- **`eq:collapse-cocycle` at the printed objects.**

`ProjectionOrbitCollapse.sub_conj_mul` proves `d_{gh} = d_g + Θ(g) d_h Θ(g)*`
in an arbitrary ring with involution, which is where the identity belongs: it
uses multiplicativity of `Θ` and nothing else.  This is that identity read at
the objects the printed proof names — the displacements of the corona
representation a coordinatewise unitary lift induces — and in the shape
`CollapseLambdaCocycle.lambda_cocycle` consumes, so the two are the same
statement about the same family. -/
theorem printedDisplacement_cocycle (P : MatFam Y)
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ))
    (p : NormMatrixCStarCorona (fun n ↦ Y n))
    (hmem : ∀ g : H,
      ProjectionOrbitCollapse.conj (coronaRepOfLift Y Θ) p g - p
        ∈ rankIdeal Y P) (g h : H) :
    ((printedDisplacement Y P Θ p hmem (g * h) : rankIdeal Y P) :
        NormMatrixCStarCorona (fun n ↦ Y n))
      = ((printedDisplacement Y P Θ p hmem g : rankIdeal Y P) :
          NormMatrixCStarCorona (fun n ↦ Y n))
        + coronaLinear Y (unitarySequenceBounded Y (Θ g)) *
            ((printedDisplacement Y P Θ p hmem h : rankIdeal Y P) :
              NormMatrixCStarCorona (fun n ↦ Y n)) *
            star (coronaLinear Y (unitarySequenceBounded Y (Θ g))) :=
  ProjectionOrbitCollapse.sub_conj_mul (coronaRepOfLift Y Θ) p g h

/-- **`CO.21` with nothing substituted.**  `β(g) = Λ(d_g)` for the printed
displacement family of the printed corona representation is a `1`-cocycle for
the printed representation `π` on the printed space `K_q`. -/
theorem printed_betaKq_cocycle (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite)
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ))
    (p : NormMatrixCStarCorona (fun n ↦ Y n))
    (hmem : ∀ g : H,
      ProjectionOrbitCollapse.conj (coronaRepOfLift Y Θ) p g - p
        ∈ rankIdeal Y P) (g h : H) :
    betaKq Y P ω hω (printedDisplacement Y P Θ p hmem) (g * h)
      = betaKq Y P ω hω (printedDisplacement Y P Θ p hmem) g
        + conjRepKq Y P ω hω Θ g
            (betaKq Y P ω hω (printedDisplacement Y P Θ p hmem) h) :=
  betaKq_cocycle Y P ω hω Θ (printedDisplacement Y P Θ p hmem)
    (printedDisplacement_cocycle Y P Θ p hmem) g h

/-- **`CO.21` and `CO.21b` joined at the printed objects.**  The printed
paragraph from `eq:collapse-cocycle` to the contradiction, with the printed
displacement family, the printed space, and the printed representation; the
only inputs are property `(T)`, the printed hypothesis on `p` at the
compressed elements, the ideal membership of the displacements, and the
nonvanishing. -/
theorem printed_collapse_contradiction_Kq (P : MatFam Y) (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ cofinite) (hT : HasKazhdanPropertyT.{u, u} H)
    (Θ : H →* (∀ n, Matrix.unitaryGroup (Y n) ℂ))
    (p : NormMatrixCStarCorona (fun n ↦ Y n)) (c : H → H)
    (hmem : ∀ g : H,
      ProjectionOrbitCollapse.conj (coronaRepOfLift Y Θ) p g - p
        ∈ rankIdeal Y P)
    (hcompressed : ∀ a : H,
      lambda Y P ω hω (printedDisplacement Y P Θ p hmem (c a)) = 0)
    (htransport : ∀ y : Kq Y P ω hω,
      (∀ a : H, conjRepKq Y P ω hω Θ (c a) y = y) →
        ∀ g : H, conjRepKq Y P ω hω Θ g y = y)
    (hne : ∃ g : H,
      lambda Y P ω hω (printedDisplacement Y P Θ p hmem g) ≠ 0) : False :=
  collapse_contradiction_Kq Y P ω hω hT Θ (printedDisplacement Y P Θ p hmem) c
    (printedDisplacement_cocycle Y P Θ p hmem) hcompressed htransport hne

end Rep

end Space

end

end CollapseInvariantSubspace
end GroupApproximation
