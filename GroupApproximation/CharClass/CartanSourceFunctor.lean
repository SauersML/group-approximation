import GroupApproximation.CharClass.CartanSourceComplex

/-!
# The source functor `X ↦ W ⊗ S(X)` and its freeness on the models

`CartanSourceComplex.lean` proves `d ∘ d = 0`.  This file packages the result as
a chain complex, makes it functorial in the space, and exhibits the freeness
hypothesis of the acyclic-models theorem.

Freeness is where the indexing chosen in `CartanDiagonalModule.lean` pays off.
`FreeOnModels` wants, in degree `k`, a `Λ`-basis of `(W ⊗ S(X))_k` indexed by
pairs of a basis index and a morphism `M (mdl k b) ⟶ X`.  Taking the models to
be the standard topological simplices and the basis index set to be
`Fin (k + 1)` — the simplex degree — that index type is
`Σ n : Fin (k+1), (stdSimplexTop n.val ⟶ X)`, which is `WSIndex k X` on the
nose.  So the basis is `Finsupp.basisSingleOne` with **no reindexing at all**,
and `basis_apply` is the statement that pushing the identity simplex forward
along `φ` gives `φ`, i.e. `Category.id_comp`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory

noncomputable section

variable (data : SingularBoundaryData)

/-! ## 1. The complex -/

/-- `W ⊗ S(X)` as a chain complex of `Λ`-modules. -/
def srcComplex (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} GroupRingZ2) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of GroupRingZ2 (WTensorSMod X k))
    (fun k => ModuleCat.ofHom (wDiff data X k))
    (fun k => by
      apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext'
      intro p
      apply LinearMap.ext_ring
      show wDiff data X k (wDiff data X (k + 1) (Finsupp.single p (1 : GroupRingZ2))) = 0
      exact wDiff_wDiff data X k p)

@[simp] theorem srcComplex_X (X : TopCat.{0}) (k : ℕ) :
    (srcComplex data X).X k = ModuleCat.of GroupRingZ2 (WTensorSMod X k) := rfl

theorem srcComplex_d (X : TopCat.{0}) (k : ℕ) :
    (srcComplex data X).d (k + 1) k = ModuleCat.ofHom (wDiff data X k) := by
  simp [srcComplex]

/-! ## 2. Functoriality -/

/-- Pushing a generator forward along a map of spaces. -/
def srcMapIdx {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) : WSIndex k X → WSIndex k Y :=
  fun p => ⟨p.1, p.2 ≫ f⟩

theorem lmapDomain_wDiffW {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (n : Fin (k + 2))
    (σ : stdSimplexTop n.val ⟶ X) :
    Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx f k) (wDiffW X k n σ)
      = wDiffW Y k n (σ ≫ f) := by
  revert σ
  induction n using Fin.lastCases with
  | last => intro σ; rw [wDiffW_last, wDiffW_last, map_zero]
  | cast j =>
      intro σ
      rw [wDiffW_castSucc, wDiffW_castSucc, map_smul, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single]
      rfl

theorem lmapDomain_wDiffS {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (n : Fin (k + 2))
    (σ : stdSimplexTop n.val ⟶ X) :
    Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx f k) (wDiffS data X k n σ)
      = wDiffS data Y k n (σ ≫ f) := by
  revert σ
  induction n using Fin.cases with
  | zero => intro σ; rw [wDiffS_zero, wDiffS_zero, map_zero]
  | succ m =>
      -- Restate the goal with the *arithmetically normalized* simplex degree
      -- before introducing the simplex.  `(Fin.succ m).val` and `m.val + 1` are
      -- definitionally equal, but a variable carrying the first form makes every
      -- later `Finsupp.single` application defeq-only, and `rw` then refuses the
      -- whole goal as "not type-correct under `instances` transparency".
      show ∀ τ : stdSimplexTop (m.val + 1) ⟶ X,
        Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx f k)
            (wDiffS data X k (Fin.succ m) τ) = wDiffS data Y k (Fin.succ m) (τ ≫ f)
      intro τ
      have hnat := data.bd_natural f m.val (Finsupp.single τ (1 : GroupRingZ2))
      rw [Finsupp.mapDomain_single] at hnat
      -- Prove the two rearrangements as freshly elaborated statements, which are
      -- type-correct at every transparency, and close the goal with `exact`.
      have hL : Finsupp.mapDomain (srcMapIdx f k)
            (Finsupp.mapDomain (fun ρ => (⟨m, ρ⟩ : WSIndex k X))
              (data.bd X m.val (Finsupp.single τ (1 : GroupRingZ2))))
          = Finsupp.mapDomain (fun ρ => (⟨m, ρ⟩ : WSIndex k Y))
              (Finsupp.mapDomain (fun x => x ≫ f)
                (data.bd X m.val (Finsupp.single τ (1 : GroupRingZ2)))) := by
        rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
        rfl
      rw [wDiffS_succ, wDiffS_succ]
      simp only [Finsupp.lmapDomain_apply]
      exact hL.trans
        (congrArg (Finsupp.mapDomain (fun ρ => (⟨m, ρ⟩ : WSIndex k Y))) hnat.symm)

theorem lmapDomain_wDiffGen {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (n : Fin (k + 2))
    (σ : stdSimplexTop n.val ⟶ X) :
    Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx f k) (wDiffGen data X k n σ)
      = wDiffGen data Y k n (σ ≫ f) := by
  rw [wDiffGen, wDiffGen, map_add, lmapDomain_wDiffW, lmapDomain_wDiffS]

/-- The chain map induced by a map of spaces. -/
def srcMap {X Y : TopCat.{0}} (f : X ⟶ Y) : srcComplex data X ⟶ srcComplex data Y where
  f k := ModuleCat.ofHom (Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx f k))
  comm' := by
    rintro i j (rfl : j + 1 = i)
    rw [srcComplex_d, srcComplex_d]
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro p
    apply LinearMap.ext_ring
    obtain ⟨n, σ⟩ := p
    show wDiff data Y j (Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx f (j + 1))
        (Finsupp.single (⟨n, σ⟩ : WSIndex (j + 1) X) (1 : GroupRingZ2)))
      = Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx f j)
          (wDiff data X j (Finsupp.single (⟨n, σ⟩ : WSIndex (j + 1) X) (1 : GroupRingZ2)))
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, wDiff_single, wDiff_single,
      lmapDomain_wDiffGen]
    rfl

/-- **The source functor** `X ↦ W ⊗ S(X)`. -/
def src : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} GroupRingZ2) ℕ where
  obj X := srcComplex data X
  map f := srcMap data f
  map_id X := by
    apply HomologicalComplex.hom_ext
    intro k
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro p
    apply LinearMap.ext_ring
    show Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx (𝟙 X) k)
        (Finsupp.single p (1 : GroupRingZ2)) = Finsupp.single p (1 : GroupRingZ2)
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    obtain ⟨n, σ⟩ := p
    show Finsupp.single (⟨n, σ ≫ 𝟙 X⟩ : WSIndex k X) 1 = _
    rw [Category.comp_id]
  map_comp {X Y Z} f g := by
    apply HomologicalComplex.hom_ext
    intro k
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro p
    apply LinearMap.ext_ring
    obtain ⟨n, σ⟩ := p
    show Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx (f ≫ g) k)
        (Finsupp.single (⟨n, σ⟩ : WSIndex k X) (1 : GroupRingZ2))
      = Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx g k)
          (Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx f k)
            (Finsupp.single (⟨n, σ⟩ : WSIndex k X) (1 : GroupRingZ2)))
    simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    show Finsupp.single (⟨n, σ ≫ f ≫ g⟩ : WSIndex k Z) 1
      = Finsupp.single (⟨n, (σ ≫ f) ≫ g⟩ : WSIndex k Z) 1
    rw [Category.assoc]

@[simp] theorem src_map_single {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (p : WSIndex k X) :
    (((src data).map f).f k).hom (Finsupp.single p (1 : GroupRingZ2))
      = Finsupp.single (srcMapIdx f k p) (1 : GroupRingZ2) := by
  show Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx f k)
      (Finsupp.single p (1 : GroupRingZ2)) = _
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-! ## 3. Freeness on the models -/

/-- **The source is free on the standard simplices.** -/
def srcFree : FreeOnModels stdSimplexTop GroupRingZ2 (src data) where
  B k := Fin (k + 1)
  mdl _ j := j.val
  gen k j := Finsupp.single (⟨j, 𝟙 (stdSimplexTop j.val)⟩ : WSIndex k (stdSimplexTop j.val))
    (1 : GroupRingZ2)
  basis X k := Finsupp.basisSingleOne
  basis_apply X k j φ := by
    rw [src_map_single]
    show Finsupp.single (⟨j, φ⟩ : WSIndex k X) (1 : GroupRingZ2)
      = Finsupp.single (⟨j, 𝟙 (stdSimplexTop j.val) ≫ φ⟩ : WSIndex k X) 1
    rw [Category.id_comp]

end

end GroupApproximation.CharClass
