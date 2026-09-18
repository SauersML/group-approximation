import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.BootstrapTwoOfThreeCone

/-!
# Two out of three for semisplit extensions: the formal reduction

Rosenberg--Schochet (*The Künneth theorem and the universal coefficient theorem for Kasparov's
generalized K-functor*, Duke Math. J. 55 (1987), §4) and Blackadar (*K-Theory for Operator
Algebras*, 22.3.5) show that the class of separable algebras `KK`-equivalent to commutative ones
has the two-out-of-three property for semisplit extensions `0 → I → A → B → 0`.  This file
carries out that argument for a `KKnFunctor` `F` equipped with a `TwoOfThreeStructure`, for the
UCT input of `thm:fixed-radical-membership` in `non_mf_group_notes.tex`.

The structure records, as data with equations wherever possible:

* **half-exactness** of `KKn(-, D)` on semisplit extensions (Cuntz--Skandalis; Blackadar 19.5.7):
  a class `x ∈ KKn(A, D)` vanishing on `I` factors through `B`;
* **excision** (Blackadar 19.5.5): the class of `excisionMap E : I → C_{E.quot}` is invertible;
* the action of the loop suspension `suspI` on classes, and **Bott periodicity**
  `S S A ∼ A` (Blackadar 19.2);
* the two facts on `K`-orthogonality used by Rosenberg--Schochet: commutative algebras are
  `K`-orthogonal (UCT for commutative algebras), and `K`-orthogonal algebras are `KK`-equivalent
  to commutative ones (realization; Meyer--Nest, Topology 45 (2006), §2).

Here `D` is *`K`-acyclic* if `KKn(ℂ, D)` and `KKn(Sℂ, D)` are trivial, and `A` is
*`K`-orthogonal* if `KKn(A, D)` and `KKn(SA, D)` are trivial for every `K`-acyclic `D`.

The proof: half-exactness gives the middle case directly on `KKn(-, D)`; the suspended middle
case uses the cone extensions of `BootstrapTwoOfThreeCone` together with excision; the other two
cases rotate the extension into `0 → SB → C_π → A → 0` and use Bott periodicity.

Main results (for `S : TwoOfThreeStructure F`):
`S.isKKnCommutative_mid`, `S.isKKnCommutative_ideal`, `S.isKKnCommutative_quot`.
-/

namespace GroupApproximation.Full.TWWUCT.Bootstrap

noncomputable section

namespace KKnFunctor

variable (F : KKnFunctor)

/-- `D` is **`K`-acyclic** for `F`: `KKn(ℂ, D)` and `KKn(Sℂ, D)` are trivial. -/
def KAcyclic (D : SepNUCStarAlgebra) : Prop :=
  Subsingleton (F.Hom (SepNUCStarAlgebra.of ℂ) D) ∧
    Subsingleton (F.Hom (SepNUCStarAlgebra.of ℂ).suspI D)

/-- `A` is **`K`-orthogonal** for `F`: `KKn(A, D)` and `KKn(SA, D)` are trivial for every
`K`-acyclic `D`. -/
def IsKOrthogonal (A : SepNUCStarAlgebra) : Prop :=
  ∀ D : SepNUCStarAlgebra, F.KAcyclic D →
    Subsingleton (F.Hom A D) ∧ Subsingleton (F.Hom A.suspI D)

variable {F}

/-- Triviality of `KKn(-, D)` is invariant under `KKn`-equivalence. -/
theorem subsingleton_of_kknEquivalent {X Y D : SepNUCStarAlgebra} (h : F.KKnEquivalent X Y)
    (hX : Subsingleton (F.Hom X D)) : Subsingleton (F.Hom Y D) := by
  obtain ⟨x, y, _, hxy⟩ := h
  refine ⟨fun a b => ?_⟩
  calc a = F.comp a (F.idHom Y) := (comp_id a).symm
    _ = F.comp a (F.comp x y) := by rw [hxy]
    _ = F.comp (F.comp a x) y := (comp_assoc a x y).symm
    _ = F.comp (F.comp b x) y :=
        congrArg (fun z => F.comp z y) (@Subsingleton.elim _ hX (F.comp a x) (F.comp b x))
    _ = F.comp b (F.comp x y) := comp_assoc b x y
    _ = F.comp b (F.idHom Y) := by rw [hxy]
    _ = b := comp_id b

end KKnFunctor

/-- **Two-out-of-three structure** on a `KKnFunctor` `F`: the ingredients of the
Rosenberg--Schochet two-out-of-three argument (Duke Math. J. 55 (1987), §4; Blackadar 22.3.5,
19.5.5, 19.5.7, 19.2).  For Cuntz's `F A = 𝒦 ⊗ qA` these are the standard properties of `KK`. -/
structure TwoOfThreeStructure (F : KKnFunctor) where
  /-- Half-exactness of `KKn(-, D)`: a factorization through the quotient of a class vanishing on
  the ideal (Blackadar 19.5.7). -/
  lift : ∀ {I A B : SepNUCStarAlgebra} (E : SemisplitExtension I A B) {D : SepNUCStarAlgebra}
    (x : F.Hom A D), F.comp x (F.classOf E.incl) = F.classOf (0 : I →⋆ₙₐ[ℂ] D) → F.Hom B D
  /-- The lift factors the class. -/
  lift_comp : ∀ {I A B : SepNUCStarAlgebra} (E : SemisplitExtension I A B)
    {D : SepNUCStarAlgebra} (x : F.Hom A D)
    (hx : F.comp x (F.classOf E.incl) = F.classOf (0 : I →⋆ₙₐ[ℂ] D)),
    F.comp (lift E x hx) (F.classOf E.quot) = x
  /-- Excision: an inverse of the class of `excisionMap E` (Blackadar 19.5.5). -/
  excisionInv : ∀ {I A B : SepNUCStarAlgebra} (E : SemisplitExtension I A B),
    F.Hom (SepNUCStarAlgebra.mappingCone E.quot) I
  excisionInv_comp : ∀ {I A B : SepNUCStarAlgebra} (E : SemisplitExtension I A B),
    F.comp (excisionInv E) (F.classOf (excisionMap E)) = F.idHom I
  comp_excisionInv : ∀ {I A B : SepNUCStarAlgebra} (E : SemisplitExtension I A B),
    F.comp (F.classOf (excisionMap E)) (excisionInv E) =
      F.idHom (SepNUCStarAlgebra.mappingCone E.quot)
  /-- The loop suspension on classes (`x ↦ x ⊗ 1_{C₀(0,1)}`). -/
  suspHom : ∀ {A B : SepNUCStarAlgebra}, F.Hom A B → F.Hom A.suspI B.suspI
  suspHom_id : ∀ A : SepNUCStarAlgebra, suspHom (F.idHom A) = F.idHom A.suspI
  suspHom_comp : ∀ {A B C : SepNUCStarAlgebra} (y : F.Hom B C) (x : F.Hom A B),
    suspHom (F.comp y x) = F.comp (suspHom y) (suspHom x)
  /-- Bott periodicity `A ∼ S S A` (Blackadar 19.2). -/
  bott : ∀ A : SepNUCStarAlgebra, F.Hom A A.suspI.suspI
  bottInv : ∀ A : SepNUCStarAlgebra, F.Hom A.suspI.suspI A
  bottInv_comp : ∀ A : SepNUCStarAlgebra, F.comp (bottInv A) (bott A) = F.idHom A
  comp_bottInv : ∀ A : SepNUCStarAlgebra, F.comp (bott A) (bottInv A) = F.idHom A.suspI.suspI
  /-- UCT for commutative algebras: they are `K`-orthogonal. -/
  isKOrthogonal_of_isCommutative : ∀ {C : SepNUCStarAlgebra}, C.IsCommutative →
    F.IsKOrthogonal C
  /-- Realization: `K`-orthogonal algebras are `KKn`-equivalent to commutative ones
  (Rosenberg--Schochet 1987, §4; Meyer--Nest 2006, §2). -/
  isKKnCommutative_of_isKOrthogonal : ∀ {A : SepNUCStarAlgebra}, F.IsKOrthogonal A →
    F.IsKKnCommutative A

namespace TwoOfThreeStructure

open KKnFunctor

variable {F : KKnFunctor}

/-- **Half-exactness in the middle**: if `KKn(I, D)` and `KKn(B, D)` are trivial, so is
`KKn(A, D)`. -/
theorem subsingleton_mid (S : TwoOfThreeStructure F) {I A B D : SepNUCStarAlgebra}
    (E : SemisplitExtension I A B) (hI : Subsingleton (F.Hom I D))
    (hB : Subsingleton (F.Hom B D)) : Subsingleton (F.Hom A D) := by
  refine ⟨fun x x' => ?_⟩
  have hx : F.comp x (F.classOf E.incl) = F.classOf (0 : I →⋆ₙₐ[ℂ] D) :=
    @Subsingleton.elim _ hI _ _
  have hx' : F.comp x' (F.classOf E.incl) = F.classOf (0 : I →⋆ₙₐ[ℂ] D) :=
    @Subsingleton.elim _ hI _ _
  calc x = F.comp (S.lift E x hx) (F.classOf E.quot) := (S.lift_comp E x hx).symm
    _ = F.comp (S.lift E x' hx') (F.classOf E.quot) :=
        congrArg (fun y => F.comp y (F.classOf E.quot))
          (@Subsingleton.elim _ hB (S.lift E x hx) (S.lift E x' hx'))
    _ = x' := S.lift_comp E x' hx'

/-- **Excision** as a `KKn`-equivalence `I ∼ C_{E.quot}`. -/
theorem kknEquivalent_excision (S : TwoOfThreeStructure F) {I A B : SepNUCStarAlgebra}
    (E : SemisplitExtension I A B) :
    F.KKnEquivalent I (SepNUCStarAlgebra.mappingCone E.quot) :=
  ⟨F.classOf (excisionMap E), S.excisionInv E, S.excisionInv_comp E, S.comp_excisionInv E⟩

/-- **Bott periodicity** as a `KKn`-equivalence `S S A ∼ A`. -/
theorem kknEquivalent_bott (S : TwoOfThreeStructure F) (A : SepNUCStarAlgebra) :
    F.KKnEquivalent A.suspI.suspI A :=
  ⟨S.bottInv A, S.bott A, S.comp_bottInv A, S.bottInv_comp A⟩

/-- `KKn`-equivalence is compatible with the loop suspension. -/
theorem kknEquivalent_suspI (S : TwoOfThreeStructure F) {X Y : SepNUCStarAlgebra}
    (h : F.KKnEquivalent X Y) : F.KKnEquivalent X.suspI Y.suspI := by
  obtain ⟨x, y, hyx, hxy⟩ := h
  refine ⟨S.suspHom x, S.suspHom y, ?_, ?_⟩
  · rw [← S.suspHom_comp y x, hyx]
    exact S.suspHom_id X
  · rw [← S.suspHom_comp x y, hxy]
    exact S.suspHom_id Y

/-- `K`-orthogonality is invariant under `KKn`-equivalence. -/
theorem isKOrthogonal_of_kknEquivalent (S : TwoOfThreeStructure F) {X Y : SepNUCStarAlgebra}
    (h : F.KKnEquivalent X Y) (hX : F.IsKOrthogonal X) : F.IsKOrthogonal Y := fun D hD =>
  ⟨subsingleton_of_kknEquivalent h (hX D hD).1,
    subsingleton_of_kknEquivalent (S.kknEquivalent_suspI h) (hX D hD).2⟩

/-- `K`-orthogonality passes to the loop suspension (by Bott periodicity). -/
theorem isKOrthogonal_suspI (S : TwoOfThreeStructure F) {X : SepNUCStarAlgebra}
    (hX : F.IsKOrthogonal X) : F.IsKOrthogonal X.suspI := fun D hD =>
  ⟨(hX D hD).2, subsingleton_of_kknEquivalent (S.kknEquivalent_bott X).symm (hX D hD).1⟩

/-- `K`-orthogonality descends from the loop suspension (by Bott periodicity). -/
theorem isKOrthogonal_of_suspI (S : TwoOfThreeStructure F) {X : SepNUCStarAlgebra}
    (hX : F.IsKOrthogonal X.suspI) : F.IsKOrthogonal X := fun D hD =>
  ⟨subsingleton_of_kknEquivalent (S.kknEquivalent_bott X) (hX D hD).2, (hX D hD).1⟩

/-- **Two out of three, middle term**: `I` and `B` `K`-orthogonal imply `A` `K`-orthogonal.
The suspended case uses the cone extensions `E₁ = coneExtension E.quot`,
`E₂ = coneExtension E₁.quot`, `E₃ = coneExtension E₂.quot` and excision for `E`, `E₁`, `E₂`. -/
theorem isKOrthogonal_mid (S : TwoOfThreeStructure F) {I A B : SepNUCStarAlgebra}
    (E : SemisplitExtension I A B) (hI : F.IsKOrthogonal I) (hB : F.IsKOrthogonal B) :
    F.IsKOrthogonal A := by
  intro D hD
  obtain ⟨hI0, hI1⟩ := hI D hD
  obtain ⟨hB0, hB1⟩ := hB D hD
  refine ⟨S.subsingleton_mid E hI0 hB0, ?_⟩
  have h₃ := S.subsingleton_mid (D := D)
    (coneExtension (coneExtension (coneExtension E.quot).quot).quot)
    (subsingleton_of_kknEquivalent (S.kknEquivalent_suspI (S.kknEquivalent_excision E)) hI1)
    (subsingleton_of_kknEquivalent (S.kknEquivalent_excision (coneExtension E.quot)) hB1)
  exact subsingleton_of_kknEquivalent
    (S.kknEquivalent_excision (coneExtension (coneExtension E.quot).quot)).symm h₃

/-- **Two out of three, ideal**: `A` and `B` `K`-orthogonal imply `I` `K`-orthogonal, via the
rotated extension `0 → S B → C_{E.quot} → A → 0` and excision `I ∼ C_{E.quot}`. -/
theorem isKOrthogonal_ideal (S : TwoOfThreeStructure F) {I A B : SepNUCStarAlgebra}
    (E : SemisplitExtension I A B) (hA : F.IsKOrthogonal A) (hB : F.IsKOrthogonal B) :
    F.IsKOrthogonal I :=
  S.isKOrthogonal_of_kknEquivalent (S.kknEquivalent_excision E).symm
    (S.isKOrthogonal_mid (coneExtension E.quot) (S.isKOrthogonal_suspI hB) hA)

/-- **Two out of three, quotient**: `I` and `A` `K`-orthogonal imply `B` `K`-orthogonal, via the
rotated extension and Bott periodicity. -/
theorem isKOrthogonal_quot (S : TwoOfThreeStructure F) {I A B : SepNUCStarAlgebra}
    (E : SemisplitExtension I A B) (hI : F.IsKOrthogonal I) (hA : F.IsKOrthogonal A) :
    F.IsKOrthogonal B :=
  S.isKOrthogonal_of_suspI
    (S.isKOrthogonal_ideal (coneExtension E.quot)
      (S.isKOrthogonal_of_kknEquivalent (S.kknEquivalent_excision E) hI) hA)

/-- Algebras `KKn`-equivalent to commutative ones are `K`-orthogonal. -/
theorem isKOrthogonal_of_isKKnCommutative (S : TwoOfThreeStructure F) {A : SepNUCStarAlgebra}
    (hA : F.IsKKnCommutative A) : F.IsKOrthogonal A := by
  obtain ⟨C, hC, hAC⟩ := hA
  exact S.isKOrthogonal_of_kknEquivalent hAC.symm (S.isKOrthogonal_of_isCommutative hC)

/-- **The `KKn`-commutative algebras are exactly the `K`-orthogonal ones.** -/
theorem isKKnCommutative_iff_isKOrthogonal (S : TwoOfThreeStructure F) (A : SepNUCStarAlgebra) :
    F.IsKKnCommutative A ↔ F.IsKOrthogonal A :=
  ⟨S.isKOrthogonal_of_isKKnCommutative, S.isKKnCommutative_of_isKOrthogonal⟩

/-- **Two out of three, middle term** (Rosenberg--Schochet 1987, §4; Blackadar 22.3.5). -/
theorem isKKnCommutative_mid (S : TwoOfThreeStructure F) {I A B : SepNUCStarAlgebra}
    (E : SemisplitExtension I A B) (hI : F.IsKKnCommutative I) (hB : F.IsKKnCommutative B) :
    F.IsKKnCommutative A :=
  S.isKKnCommutative_of_isKOrthogonal
    (S.isKOrthogonal_mid E (S.isKOrthogonal_of_isKKnCommutative hI)
      (S.isKOrthogonal_of_isKKnCommutative hB))

/-- **Two out of three, ideal** (Rosenberg--Schochet 1987, §4; Blackadar 22.3.5). -/
theorem isKKnCommutative_ideal (S : TwoOfThreeStructure F) {I A B : SepNUCStarAlgebra}
    (E : SemisplitExtension I A B) (hA : F.IsKKnCommutative A) (hB : F.IsKKnCommutative B) :
    F.IsKKnCommutative I :=
  S.isKKnCommutative_of_isKOrthogonal
    (S.isKOrthogonal_ideal E (S.isKOrthogonal_of_isKKnCommutative hA)
      (S.isKOrthogonal_of_isKKnCommutative hB))

/-- **Two out of three, quotient** (Rosenberg--Schochet 1987, §4; Blackadar 22.3.5). -/
theorem isKKnCommutative_quot (S : TwoOfThreeStructure F) {I A B : SepNUCStarAlgebra}
    (E : SemisplitExtension I A B) (hI : F.IsKKnCommutative I) (hA : F.IsKKnCommutative A) :
    F.IsKKnCommutative B :=
  S.isKKnCommutative_of_isKOrthogonal
    (S.isKOrthogonal_quot E (S.isKOrthogonal_of_isKKnCommutative hI)
      (S.isKOrthogonal_of_isKKnCommutative hA))

end TwoOfThreeStructure

end

end GroupApproximation.Full.TWWUCT.Bootstrap
