import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVCohnK2.MoritaMap
import GroupApproximation.Steinberg.Functoriality

/-!
# Properties of the block map (lane LVCohnK2)

`simple_kazhdan_sofic_group.tex` l.733-735 (`sec:questions`), leaf T1b.iii.  For the Morita
invariance of stable `K₂` (Ara–Brustenga–Cortiñas 2009, ultramatricial stages of the Cohn algebra)
we prove that `blockMap hI : St_{I×J}(R) →* St_I(M_J(R))`

* is surjective (`blockMap_surjective`);
* covers block flattening `GL_I(M_J(R)) ≅ GL_{I×J}(R)` (`blockUnitHom_blockMap`), so it maps only
  `K₂(I × J, R)` into `K₂(I, M_J(R))` (`projection_eq_one_of_blockMap`);
* is compatible with padding of the first index (`blockMap_indexMap`).
-/

namespace GroupApproximation.Full.LVCohnK2

open SteinbergGroup
open scoped commutatorElement

variable {I : Type*} [Fintype I] [DecidableEq I] {J : Type*} [Fintype J] [DecidableEq J]
  {R : Type*} [Ring R]

/-- `blockMap` is surjective: `x_{ij}(M)` is a product of images of `x_{(i,k),(j,l)}(a)`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem blockMap_surjective (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c) :
    Function.Surjective (blockMap (J := J) (R := R) hI) := by
  intro y
  have hy : y ∈ (blockMap (J := J) (R := R) hI).range := by
    refine PresentedGroup.generated_by (relations (I := I) (R := Matrix J J R))
      (blockMap (J := J) (R := R) hI).range ?_ y
    rintro ⟨i, j, hij, M⟩
    change x i j hij M ∈ (blockMap (J := J) (R := R) hI).range
    induction M using Matrix.induction_on' with
    | h_zero =>
        rw [x_zero]
        exact one_mem _
    | h_add M N hM hN =>
        rw [← x_mul]
        exact mul_mem hM hN
    | h_std_basis k l a =>
        refine MonoidHom.mem_range.mpr
          ⟨x (i, k) (j, l) (fun h => hij (congrArg Prod.fst h)) a, ?_⟩
        exact blockMap_x_ne hI i j k l _ hij a
  exact MonoidHom.mem_range.mp hy

/-- The composite `St_I(M_J(R)) → E_I(M_J(R)) → GL_{I×J}(R)` (projection followed by block
flattening).  (`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
noncomputable def blockUnitHom :
    SteinbergGroup I (Matrix J J R) →* (Matrix (I × J) (I × J) R)ˣ :=
  (elementaryBlockUnitEquiv (ι := I) (κ := J) (R := R)).toMonoidHom.comp
    ((elementaryGroup I (Matrix J J R)).subtype.comp (projection (I := I) (R := Matrix J J R)))

/-- `blockUnitHom` on root elements with coefficient `e_{kl} a`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem blockUnitHom_x (i j : I) (hij : i ≠ j) (k l : J) (a : R) :
    blockUnitHom (x i j hij (Matrix.single k l a)) =
      elementaryUnit (i, k) (j, l) (fun h => hij (congrArg Prod.fst h)) a := by
  rw [blockUnitHom, MonoidHom.comp_apply, MonoidHom.comp_apply, projection_x]
  exact elementaryBlockUnitEquiv_single i j hij k l a

/-- `blockUnitHom` on the diagonal block generators.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem blockUnitHom_diagElem (i p : I) (hip : i ≠ p) (k l : J) (hlk : l ≠ k) (a : R) :
    blockUnitHom (diagElem i p hip k l a) =
      elementaryUnit (i, k) (i, l) (fun h => hlk (congrArg Prod.snd h).symm) a := by
  rw [diagElem, map_commutatorElement, blockUnitHom_x i p hip k l a,
    blockUnitHom_x p i hip.symm l l (1 : R),
    elementaryUnit_commutator (i, k) (p, l) (i, l) (fun h => hip (congrArg Prod.fst h))
      (fun h => hip.symm (congrArg Prod.fst h)) (fun h => hlk (congrArg Prod.snd h).symm) a 1,
    mul_one]

/-- `blockMap` covers block flattening of elementary matrices.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem blockUnitHom_blockMap (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c)
    (g : SteinbergGroup (I × J) R) :
    blockUnitHom (blockMap hI g) =
      ((projection g : elementaryGroup (I × J) R) : (Matrix (I × J) (I × J) R)ˣ) := by
  have hh : (blockUnitHom (I := I) (J := J) (R := R)).comp (blockMap hI) =
      (elementaryGroup (I × J) R).subtype.comp (projection (I := I × J) (R := R)) := by
    refine PresentedGroup.ext ?_
    rintro ⟨⟨i, k⟩, ⟨j, l⟩, h, a⟩
    change blockUnitHom (blockMap hI (x (i, k) (j, l) h a)) =
      ((projection (x (i, k) (j, l) h a) : elementaryGroup (I × J) R) :
        (Matrix (I × J) (I × J) R)ˣ)
    rw [projection_x, elementaryRoot_val]
    by_cases hij : i = j
    · subst hij
      rw [blockMap_x_eq hI i k l h a,
        blockUnitHom_diagElem i (auxIndex hI i) (auxIndex_ne hI i) k l (pair_snd_ne h).symm a]
    · rw [blockMap_x_ne hI i j k l h hij a, blockUnitHom_x i j hij k l a]
  exact DFunLike.congr_fun hh g

/-- `blockMap` maps only `K₂(I × J, R)` into `K₂(I, M_J(R))`.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem projection_eq_one_of_blockMap (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c)
    (g : SteinbergGroup (I × J) R) (hg : projection (blockMap hI g) = 1) : projection g = 1 := by
  have h : ((projection g : elementaryGroup (I × J) R) : (Matrix (I × J) (I × J) R)ˣ) = 1 := by
    rw [← blockUnitHom_blockMap hI g, blockUnitHom, MonoidHom.comp_apply, MonoidHom.comp_apply,
      hg, map_one, map_one]
  exact OneMemClass.coe_eq_one.mp h

/-- Padding commutes with diagonal block generators.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem indexMap_diagElem {I' : Type*} [Fintype I'] [DecidableEq I'] (e : I ↪ I') (i p : I)
    (hip : i ≠ p) (k l : J) (a : R) :
    indexMap e (diagElem i p hip k l a) = diagElem (e i) (e p) (e.injective.ne hip) k l a := by
  unfold diagElem
  rw [map_commutatorElement, indexMap_x, indexMap_x]

/-- `blockMap` is compatible with padding of the first index.
(`simple_kazhdan_sofic_group.tex` l.733-735, leaf T1b.iii.) -/
theorem blockMap_indexMap {I' : Type*} [Fintype I'] [DecidableEq I']
    (hI : ∀ a b c : I, ∃ d : I, d ≠ a ∧ d ≠ b ∧ d ≠ c)
    (hI' : ∀ a b c : I', ∃ d : I', d ≠ a ∧ d ≠ b ∧ d ≠ c) (e : I ↪ I')
    (g : SteinbergGroup (I × J) R) :
    blockMap hI' (indexMap (e.prodMap (Function.Embedding.refl J)) g) =
      indexMap e (blockMap hI g) := by
  have hh : (blockMap (J := J) (R := R) hI').comp
      (indexMap (e.prodMap (Function.Embedding.refl J))) =
      (indexMap (R := Matrix J J R) e).comp (blockMap hI) := by
    refine PresentedGroup.ext ?_
    rintro ⟨⟨i, k⟩, ⟨j, l⟩, h, a⟩
    change blockMap hI' (indexMap (e.prodMap (Function.Embedding.refl J)) (x (i, k) (j, l) h a)) =
      indexMap e (blockMap hI (x (i, k) (j, l) h a))
    rw [indexMap_x]
    by_cases hij : i = j
    · subst hij
      have h' : (e i, k) ≠ (e i, l) := fun h2 => pair_snd_ne h (congrArg Prod.snd h2)
      rw [blockMap_x_eq hI i k l h a, indexMap_diagElem]
      exact (blockMap_x_eq hI' (e i) k l h' a).trans
        (diagElem_indep (e i) (auxIndex hI' (e i)) (e (auxIndex hI i)) (auxIndex_ne hI' (e i))
          (e.injective.ne (auxIndex_ne hI i)) k l (pair_snd_ne h).symm a)
    · have hij' : e i ≠ e j := e.injective.ne hij
      have h' : (e i, k) ≠ (e j, l) := fun h2 => hij' (congrArg Prod.fst h2)
      rw [blockMap_x_ne hI i j k l h hij a, indexMap_x]
      exact blockMap_x_ne hI' (e i) (e j) k l h' hij' a
  exact DFunLike.congr_fun hh g

end GroupApproximation.Full.LVCohnK2
