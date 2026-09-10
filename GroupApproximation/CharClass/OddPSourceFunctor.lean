import GroupApproximation.CharClass.OddPSourceDD
import GroupApproximation.CharClass.CartanSourceFunctor

/-!
# The source functor `X ↦ W ⊗ C(X)` at odd `p`

`OddPSourceDD.lean` proves `d ∘ d = 0`; this file packages it as a chain
complex and makes it functorial in the space.  It is `CartanSourceFunctor.lean`
with the coefficient ring changed and no new mathematics: the two scalars that
distinguish odd `p` — the alternating resolution coefficient and the Koszul sign
— are **scalars**, and a `Finsupp.lmapDomain` is linear, so both cross the
pushforward by `map_smul` and neither appears in a naturality argument.

`srcMapIdx` is **reused** from `CartanSourceFunctor.lean` rather than redefined:
like `WSIndex` and `stdSimplexTop`, it does not mention the coefficient ring, and
a second declaration of it in this namespace would be a root-only failure that no
probe sees.

## A correction to this lane's own plan

The plan (§2.3) repeated cc-cartan's report that the `FreeOnModels` basis needs a
`ULift` reindex, "spent in the `basis`/`basis_apply` fields and nowhere else".
Reading the landed `srcFree` shows it does not: they index the degree-`k` carrier
by `Σ n : Fin (k+1), (stdSimplexTop n.val ⟶ X)`, the **bare hom-set**, which is
what `FreeOnModels` wants on the nose, so the basis is `Finsupp.basisSingleOne`
with no reindexing at all.  The report's remark was true of an earlier design.
This lane inherits the good one; see `OddPSourceFree.lean`.
-/

namespace GroupApproximation.CharClass

open CategoryTheory

noncomputable section

variable (p : ℕ) (data : OddPBoundaryData p)

/-! ## 1. The complex -/

/-- `W ⊗ C(X)` as a chain complex of `Λ`-modules at odd `p`. -/
def oddSrcComplex (X : TopCat.{0}) : ChainComplex (ModuleCat.{0} (GroupRingZMod p)) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of (GroupRingZMod p) (OddWTensor p k X))
    (fun k => ModuleCat.ofHom (oddDiff p data X k))
    (fun k => by
      apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext'
      intro q
      apply LinearMap.ext_ring
      show oddDiff p data X k
          (oddDiff p data X (k + 1) (Finsupp.single q (1 : GroupRingZMod p))) = 0
      exact oddDiff_oddDiff p data X k q)

@[simp] theorem oddSrcComplex_X (X : TopCat.{0}) (k : ℕ) :
    (oddSrcComplex p data X).X k = ModuleCat.of (GroupRingZMod p) (OddWTensor p k X) := rfl

theorem oddSrcComplex_d (X : TopCat.{0}) (k : ℕ) :
    (oddSrcComplex p data X).d (k + 1) k = ModuleCat.ofHom (oddDiff p data X k) := by
  simp [oddSrcComplex]

/-! ## 2. Functoriality -/

theorem lmapDomain_oddDiffW {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (n : Fin (k + 2))
    (σ : stdSimplexTop n.val ⟶ X) :
    Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (srcMapIdx f k)
        (oddDiffW p X k n σ)
      = oddDiffW p Y k n (σ ≫ f) := by
  revert σ
  induction n using Fin.lastCases with
  | last => intro σ; rw [oddDiffW_last, oddDiffW_last, map_zero]
  | cast j =>
      intro σ
      rw [oddDiffW_castSucc, oddDiffW_castSucc, map_smul, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_single]
      rfl

theorem lmapDomain_oddDiffS {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (n : Fin (k + 2))
    (σ : stdSimplexTop n.val ⟶ X) :
    Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (srcMapIdx f k)
        (oddDiffS p data X k n σ)
      = oddDiffS p data Y k n (σ ≫ f) := by
  revert σ
  induction n using Fin.cases with
  | zero => intro σ; rw [oddDiffS_zero, oddDiffS_zero, map_zero]
  | succ m =>
      -- Restate with the arithmetically normalized simplex degree *before*
      -- introducing the simplex: a variable carrying `(Fin.succ m).val` makes
      -- every later `Finsupp.single` defeq-only, and `rw` then refuses the whole
      -- goal as not type-correct under `instances` transparency.  This lane paid
      -- two probe rounds for the same shape elsewhere.
      show ∀ τ : stdSimplexTop (m.val + 1) ⟶ X,
        Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (srcMapIdx f k)
            (oddDiffS p data X k (Fin.succ m) τ)
          = oddDiffS p data Y k (Fin.succ m) (τ ≫ f)
      intro τ
      have hnat := data.bd_natural f m.val (Finsupp.single τ (1 : GroupRingZMod p))
      rw [Finsupp.mapDomain_single] at hnat
      have hL : Finsupp.mapDomain (srcMapIdx f k)
            (Finsupp.mapDomain (fun ρ => (⟨m, ρ⟩ : WSIndex k X))
              (data.bd X m.val (Finsupp.single τ (1 : GroupRingZMod p))))
          = Finsupp.mapDomain (fun ρ => (⟨m, ρ⟩ : WSIndex k Y))
              (Finsupp.mapDomain (fun x => x ≫ f)
                (data.bd X m.val (Finsupp.single τ (1 : GroupRingZMod p)))) := by
        rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
        rfl
      rw [oddDiffS_succ, oddDiffS_succ, map_smul]
      simp only [Finsupp.lmapDomain_apply]
      exact congrArg (fun z : OddWTensor p k Y =>
          ((-1 : GroupRingZMod p) ^ (k - m.val)) • z)
        (hL.trans (congrArg (Finsupp.mapDomain (fun ρ => (⟨m, ρ⟩ : WSIndex k Y)))
          hnat.symm))

theorem lmapDomain_oddDiffGen {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ) (n : Fin (k + 2))
    (σ : stdSimplexTop n.val ⟶ X) :
    Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (srcMapIdx f k)
        (oddDiffGen p data X k n σ)
      = oddDiffGen p data Y k n (σ ≫ f) := by
  rw [oddDiffGen, oddDiffGen, map_add, lmapDomain_oddDiffW, lmapDomain_oddDiffS]

/-- The chain map induced by a map of spaces. -/
def oddSrcMap {X Y : TopCat.{0}} (f : X ⟶ Y) :
    oddSrcComplex p data X ⟶ oddSrcComplex p data Y where
  f k := ModuleCat.ofHom
    (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (srcMapIdx f k))
  comm' := by
    rintro i j (rfl : j + 1 = i)
    rw [oddSrcComplex_d, oddSrcComplex_d]
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro q
    apply LinearMap.ext_ring
    obtain ⟨n, σ⟩ := q
    show oddDiff p data Y j
        (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (srcMapIdx f (j + 1))
          (Finsupp.single (⟨n, σ⟩ : WSIndex (j + 1) X) (1 : GroupRingZMod p)))
      = Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (srcMapIdx f j)
          (oddDiff p data X j
            (Finsupp.single (⟨n, σ⟩ : WSIndex (j + 1) X) (1 : GroupRingZMod p)))
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, oddDiff_single,
      oddDiff_single, lmapDomain_oddDiffGen]
    rfl

/-- **The source functor** `X ↦ W ⊗ C(X)` at odd `p`. -/
def oddSrc : TopCat.{0} ⥤ ChainComplex (ModuleCat.{0} (GroupRingZMod p)) ℕ where
  obj X := oddSrcComplex p data X
  map f := oddSrcMap p data f
  map_id X := by
    apply HomologicalComplex.hom_ext
    intro k
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro q
    apply LinearMap.ext_ring
    show Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (srcMapIdx (𝟙 X) k)
        (Finsupp.single q (1 : GroupRingZMod p)) = Finsupp.single q (1 : GroupRingZMod p)
    rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    obtain ⟨n, σ⟩ := q
    show Finsupp.single (⟨n, σ ≫ 𝟙 X⟩ : WSIndex k X) 1 = _
    rw [Category.comp_id]
  map_comp {X Y Z} f g := by
    apply HomologicalComplex.hom_ext
    intro k
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext'
    intro q
    apply LinearMap.ext_ring
    obtain ⟨n, σ⟩ := q
    show Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (srcMapIdx (f ≫ g) k)
        (Finsupp.single (⟨n, σ⟩ : WSIndex k X) (1 : GroupRingZMod p))
      = Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (srcMapIdx g k)
          (Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (srcMapIdx f k)
            (Finsupp.single (⟨n, σ⟩ : WSIndex k X) (1 : GroupRingZMod p)))
    simp only [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    show Finsupp.single (⟨n, σ ≫ f ≫ g⟩ : WSIndex k Z) 1
      = Finsupp.single (⟨n, (σ ≫ f) ≫ g⟩ : WSIndex k Z) 1
    rw [Category.assoc]

@[simp] theorem oddSrc_map_single {X Y : TopCat.{0}} (f : X ⟶ Y) (k : ℕ)
    (q : WSIndex k X) :
    (((oddSrc p data).map f).f k).hom (Finsupp.single q (1 : GroupRingZMod p))
      = Finsupp.single (srcMapIdx f k q) (1 : GroupRingZMod p) := by
  show Finsupp.lmapDomain (GroupRingZMod p) (GroupRingZMod p) (srcMapIdx f k)
      (Finsupp.single q (1 : GroupRingZMod p)) = _
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

end

end GroupApproximation.CharClass
