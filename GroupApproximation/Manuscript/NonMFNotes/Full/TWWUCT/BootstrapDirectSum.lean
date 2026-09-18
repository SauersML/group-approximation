import GroupApproximation.Manuscript.NonMFNotes.Full.TWWUCT.BootstrapClosureFunctorial

/-!
# Finite direct sums as a `KKn`-bifunctor

Rosenberg--Schochet (Duke Math. J. 55 (1987), §2) and Blackadar (*K-Theory for Operator
Algebras*, 19.x, 22.3.4) use that the direct sum `A ⊕ B` is functorial on `KK`-classes, so that
the class of algebras `KK`-equivalent to commutative ones is closed under finite direct sums.
This file supplies that step for the UCT input of `thm:fixed-radical-membership` in
`non_mf_group_notes.tex`.

* `prodMap f g : D × E →⋆ₙₐ[ℂ] D' × E'`, its functoriality, and its compatibility with homotopy
  (`nHomotopic_prodMap`);
* `prodClass`, the induced map on homotopy classes, with `prodClass_id` and `prodClass_comp`;
* `DirectSumStructure F`: for a `KKnFunctor` `F`, a homotopy equivalence
  `F (A ⊕ B) ≃ₕ F A ⊕ F B` (Cuntz, *A new look at KK-theory*, K-Theory 1 (1987): for
  `F A = 𝒦 ⊗ qA` this is the additivity of `KK`);
* `directSumBifunctor F S : KKnBifunctor F` with `objOp := SepNUCStarAlgebra.prod`;
* the corollaries `isKKnCommutative_prod`, `kknEquivalent_prod` and
  `isKKnCommutative_foldr_prod` (finite iterated direct sums).
-/

namespace GroupApproximation.Full.TWWUCT.Bootstrap

open GroupApproximation.Full.TWWKK

noncomputable section

section ProdMap

variable {D : Type*} {E : Type*} {D' : Type*} {E' : Type*} {D'' : Type*} {E'' : Type*}
variable [NonUnitalCStarAlgebra D] [NonUnitalCStarAlgebra E] [NonUnitalCStarAlgebra D']
  [NonUnitalCStarAlgebra E'] [NonUnitalCStarAlgebra D''] [NonUnitalCStarAlgebra E'']

/-- **The direct sum of two `⋆`-homomorphisms**, `(x, y) ↦ (f x, g y)`. -/
def prodMap (f : D →⋆ₙₐ[ℂ] D') (g : E →⋆ₙₐ[ℂ] E') : D × E →⋆ₙₐ[ℂ] D' × E' :=
  (f.comp (NonUnitalStarAlgHom.fst ℂ D E)).prod (g.comp (NonUnitalStarAlgHom.snd ℂ D E))

theorem prodMap_apply (f : D →⋆ₙₐ[ℂ] D') (g : E →⋆ₙₐ[ℂ] E') (x : D × E) :
    prodMap f g x = (f x.1, g x.2) :=
  rfl

theorem prodMap_id :
    prodMap (NonUnitalStarAlgHom.id ℂ D) (NonUnitalStarAlgHom.id ℂ E) =
      NonUnitalStarAlgHom.id ℂ (D × E) :=
  NonUnitalStarAlgHom.ext fun _ => rfl

theorem prodMap_comp (f : D →⋆ₙₐ[ℂ] D') (f' : D' →⋆ₙₐ[ℂ] D'') (g : E →⋆ₙₐ[ℂ] E')
    (g' : E' →⋆ₙₐ[ℂ] E'') :
    prodMap (f'.comp f) (g'.comp g) = (prodMap f' g').comp (prodMap f g) :=
  NonUnitalStarAlgHom.ext fun _ => rfl

/-- **Direct sums preserve homotopy.** -/
theorem nHomotopic_prodMap {f₀ f₁ : D →⋆ₙₐ[ℂ] D'} {g₀ g₁ : E →⋆ₙₐ[ℂ] E'}
    (hf : NHomotopic f₀ f₁) (hg : NHomotopic g₀ g₁) :
    NHomotopic (prodMap f₀ g₀) (prodMap f₁ g₁) := by
  obtain ⟨p, hp, hp0, hp1⟩ := hf
  obtain ⟨q, hq, hq0, hq1⟩ := hg
  refine ⟨fun t => prodMap (p t) (q t), fun x => (hp x.1).prodMk (hq x.2), ?_, ?_⟩
  · show prodMap (p 0) (q 0) = prodMap f₀ g₀
    rw [hp0, hq0]
  · show prodMap (p 1) (q 1) = prodMap f₁ g₁
    rw [hp1, hq1]

/-- **The direct sum of homotopy classes.** -/
def prodClass (x : HomotopyClass D D') (y : HomotopyClass E E') :
    HomotopyClass (D × E) (D' × E') :=
  Quot.lift
    (fun f : D →⋆ₙₐ[ℂ] D' =>
      Quot.lift (fun g : E →⋆ₙₐ[ℂ] E' => HomotopyClass.mk (prodMap f g))
        (fun _ _ h =>
          HomotopyClass.mk_eq_mk_of_nHomotopic (nHomotopic_prodMap (NHomotopic.refl f) h)) y)
    (fun _ _ h => by
      induction y using HomotopyClass.ind with
      | mk g =>
        exact HomotopyClass.mk_eq_mk_of_nHomotopic (nHomotopic_prodMap h (NHomotopic.refl g)))
    x

theorem prodClass_mk (f : D →⋆ₙₐ[ℂ] D') (g : E →⋆ₙₐ[ℂ] E') :
    prodClass (HomotopyClass.mk f) (HomotopyClass.mk g) = HomotopyClass.mk (prodMap f g) :=
  rfl

theorem prodClass_id :
    prodClass (HomotopyClass.id D) (HomotopyClass.id E) = HomotopyClass.id (D × E) := by
  show HomotopyClass.mk (prodMap (NonUnitalStarAlgHom.id ℂ D) (NonUnitalStarAlgHom.id ℂ E)) =
    HomotopyClass.mk (NonUnitalStarAlgHom.id ℂ (D × E))
  rw [prodMap_id]

theorem prodClass_comp (x' : HomotopyClass D' D'') (x : HomotopyClass D D')
    (y' : HomotopyClass E' E'') (y : HomotopyClass E E') :
    prodClass (HomotopyClass.comp x' x) (HomotopyClass.comp y' y) =
      HomotopyClass.comp (prodClass x' y') (prodClass x y) := by
  induction x using HomotopyClass.ind with
  | mk f =>
    induction x' using HomotopyClass.ind with
    | mk f' =>
      induction y using HomotopyClass.ind with
      | mk g =>
        induction y' using HomotopyClass.ind with
        | mk g' =>
          show HomotopyClass.mk (prodMap (f'.comp f) (g'.comp g)) =
            HomotopyClass.mk ((prodMap f' g').comp (prodMap f g))
          rw [prodMap_comp]

end ProdMap

/-- **Direct-sum structure** on a `KKnFunctor` `F`: homotopy equivalences
`F (A ⊕ B) ≃ₕ F A ⊕ F B` (no naturality is required).  For Cuntz's `F A = 𝒦 ⊗ qA` these
are `split = (F π₁, F π₂)` and `join = F ι₁ ∘ fst ⊕ F ι₂ ∘ snd` (Cuntz sum), the homotopies
being the additivity of `KK` (Cuntz 1987, §3; Blackadar 17.8, 19.x). -/
structure DirectSumStructure (F : KKnFunctor) where
  /-- `F (A ⊕ B) → F A ⊕ F B`. -/
  split : ∀ A B : SepNUCStarAlgebra, F.obj (A.prod B) →⋆ₙₐ[ℂ] F.obj A × F.obj B
  /-- `F A ⊕ F B → F (A ⊕ B)`. -/
  join : ∀ A B : SepNUCStarAlgebra, F.obj A × F.obj B →⋆ₙₐ[ℂ] F.obj (A.prod B)
  /-- `join ∘ split ≃ id`. -/
  join_split : ∀ A B : SepNUCStarAlgebra,
    NHomotopic ((join A B).comp (split A B)) (NonUnitalStarAlgHom.id ℂ (F.obj (A.prod B)))
  /-- `split ∘ join ≃ id`. -/
  split_join : ∀ A B : SepNUCStarAlgebra,
    NHomotopic ((split A B).comp (join A B)) (NonUnitalStarAlgHom.id ℂ (F.obj A × F.obj B))

namespace DirectSumStructure

variable {F : KKnFunctor} (S : DirectSumStructure F)

/-- The direct sum of `KKn`-classes: `[join] ∘ (x ⊕ y) ∘ [split]`. -/
def homOp {A A' B B' : SepNUCStarAlgebra} (x : F.Hom A A') (y : F.Hom B B') :
    F.Hom (A.prod B) (A'.prod B') :=
  HomotopyClass.comp (HomotopyClass.mk (S.join A' B'))
    (HomotopyClass.comp (prodClass x y) (HomotopyClass.mk (S.split A B)))

theorem split_join_class (A B : SepNUCStarAlgebra) :
    HomotopyClass.comp (HomotopyClass.mk (S.split A B)) (HomotopyClass.mk (S.join A B)) =
      HomotopyClass.id (F.obj A × F.obj B) :=
  HomotopyClass.mk_eq_mk_of_nHomotopic (S.split_join A B)

theorem split_join_comp {C : Type*} [NonUnitalCStarAlgebra C] (A B : SepNUCStarAlgebra)
    (z : HomotopyClass C (F.obj A × F.obj B)) :
    HomotopyClass.comp (HomotopyClass.mk (S.split A B))
      (HomotopyClass.comp (HomotopyClass.mk (S.join A B)) z) = z := by
  rw [← HomotopyClass.comp_assoc, S.split_join_class A B, HomotopyClass.id_comp]

theorem homOp_id (A B : SepNUCStarAlgebra) :
    S.homOp (F.idHom A) (F.idHom B) = F.idHom (A.prod B) := by
  show HomotopyClass.comp (HomotopyClass.mk (S.join A B))
      (HomotopyClass.comp (prodClass (HomotopyClass.id (F.obj A)) (HomotopyClass.id (F.obj B)))
        (HomotopyClass.mk (S.split A B))) = HomotopyClass.id (F.obj (A.prod B))
  rw [prodClass_id, HomotopyClass.id_comp]
  exact HomotopyClass.mk_eq_mk_of_nHomotopic (S.join_split A B)

theorem homOp_comp {A A' A'' B B' B'' : SepNUCStarAlgebra} (x' : F.Hom A' A'')
    (x : F.Hom A A') (y' : F.Hom B' B'') (y : F.Hom B B') :
    S.homOp (F.comp x' x) (F.comp y' y) = F.comp (S.homOp x' y') (S.homOp x y) := by
  show HomotopyClass.comp (HomotopyClass.mk (S.join A'' B''))
      (HomotopyClass.comp (prodClass (HomotopyClass.comp x' x) (HomotopyClass.comp y' y))
        (HomotopyClass.mk (S.split A B))) =
    HomotopyClass.comp
      (HomotopyClass.comp (HomotopyClass.mk (S.join A'' B''))
        (HomotopyClass.comp (prodClass x' y') (HomotopyClass.mk (S.split A' B'))))
      (HomotopyClass.comp (HomotopyClass.mk (S.join A' B'))
        (HomotopyClass.comp (prodClass x y) (HomotopyClass.mk (S.split A B))))
  rw [prodClass_comp]
  simp only [HomotopyClass.comp_assoc]
  rw [S.split_join_comp A' B']

end DirectSumStructure

/-- **The direct sum `KKn`-bifunctor** `(A, B) ↦ A ⊕ B` of a functor with a direct-sum
structure. -/
def directSumBifunctor (F : KKnFunctor) (S : DirectSumStructure F) : KKnBifunctor F where
  objOp := SepNUCStarAlgebra.prod
  homOp x y := S.homOp x y
  homOp_id := S.homOp_id
  homOp_comp := S.homOp_comp

theorem directSumBifunctor_objOp (F : KKnFunctor) (S : DirectSumStructure F)
    (A B : SepNUCStarAlgebra) : (directSumBifunctor F S).objOp A B = A.prod B :=
  rfl

section Corollaries

variable {F : KKnFunctor}

/-- **`KKn`-equivalence is compatible with direct sums.** -/
theorem kknEquivalent_prod (S : DirectSumStructure F) {A A' B B' : SepNUCStarAlgebra}
    (hA : F.KKnEquivalent A A')
    (hB : F.KKnEquivalent B B') : F.KKnEquivalent (A.prod B) (A'.prod B') :=
  (directSumBifunctor F S).kknEquivalent hA hB

/-- **Closure under direct sums** (Rosenberg--Schochet 1987, §2; Blackadar 22.3.4). -/
theorem isKKnCommutative_prod (S : DirectSumStructure F) {A B : SepNUCStarAlgebra}
    (hA : F.IsKKnCommutative A)
    (hB : F.IsKKnCommutative B) : F.IsKKnCommutative (A.prod B) :=
  (directSumBifunctor F S).isKKnCommutative
    (fun _ _ hC hD => SepNUCStarAlgebra.IsCommutative.prod hC hD) hA hB

/-- **Closure under finite direct sums** `A₁ ⊕ (A₂ ⊕ (⋯ ⊕ Z))`. -/
theorem isKKnCommutative_foldr_prod (S : DirectSumStructure F) {Z : SepNUCStarAlgebra}
    (hZ : F.IsKKnCommutative Z)
    (L : List SepNUCStarAlgebra) (hL : ∀ A ∈ L, F.IsKKnCommutative A) :
    F.IsKKnCommutative (L.foldr SepNUCStarAlgebra.prod Z) :=
  (directSumBifunctor F S).isKKnCommutative_foldr
    (fun _ _ hC hD => SepNUCStarAlgebra.IsCommutative.prod hC hD) hZ L hL

end Corollaries

end

end GroupApproximation.Full.TWWUCT.Bootstrap
