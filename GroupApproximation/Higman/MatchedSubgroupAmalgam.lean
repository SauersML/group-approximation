import GroupApproximation.Sofic.SymmetricDoubleSubgroupReflection
import GroupApproximation.Higman.AmalgamPushout
import GroupApproximation.Algebra.PushoutITorsionFree

/-!
# Matched subgroups embed as a sub-amalgam

Suppose `M` embeds in two groups `A` and `B`, and subgroups `Z ≤ A` and
`Q ≤ B` pull back to the same subgroup `Delta ≤ M`.  Then the small amalgam

`Z *_Delta Q`

maps injectively into `A *_M B`.  Its range is exactly the subgroup generated
by the images of `Z` and `Q`.

This is the structural half of the matched-subgroup descent used by the
paired-return cutter.  Injectivity is an application of the repository's
internal Bass--Serre base-change theorem; the two exact comap identities are
used precisely to show that the factor inclusions reflect membership in the
large edge group.  No conclusion-shaped hypothesis is present.
-/

namespace GroupApproximation
namespace Higman
namespace MatchedSubgroupAmalgam

open Monoid

variable {M₀ A B : Type}
  [Group M₀] [Group A] [Group B]
  (eA : M₀ →* A) (eB : M₀ →* B)
  (Z : Subgroup A) (Q : Subgroup B) (Delta : Subgroup M₀)

/-- The edge map from the matched subgroup into the left small factor. -/
def edgeToZ (hZ : Z.comap eA = Delta) : ↥Delta →* ↥Z :=
  ((eA.comp Delta.subtype).codRestrict Z fun d => by
    have hd : (d : M₀) ∈ Z.comap eA := by
      rw [hZ]
      exact d.property
    exact hd)

/-- The edge map from the matched subgroup into the right small factor. -/
def edgeToQ (hQ : Q.comap eB = Delta) : ↥Delta →* ↥Q :=
  ((eB.comp Delta.subtype).codRestrict Q fun d => by
    have hd : (d : M₀) ∈ Q.comap eB := by
      rw [hQ]
      exact d.property
    exact hd)

/-- The two-factor diagram for the small amalgam. -/
def smallEdge (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    ∀ b : Bool, ↥Delta →* Amalgam.fam ↥Z ↥Q b
  | false => edgeToZ eA Z Delta hZ
  | true => edgeToQ eB Q Delta hQ

/-- The factorwise inclusion of the small diagram into the large diagram. -/
def factorInclusion :
    ∀ b : Bool, Amalgam.fam ↥Z ↥Q b →* Amalgam.fam A B b
  | false => Z.subtype
  | true => Q.subtype

/-- The matched edge subgroup includes into the large edge group. -/
def edgeInclusion : ↥Delta →* M₀ := Delta.subtype

theorem factorInclusion_commutes
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    ∀ b, (factorInclusion Z Q b).comp (smallEdge eA eB Z Q Delta hZ hQ b) =
      (Amalgam.famHom eA eB b).comp (edgeInclusion Delta) := by
  intro b
  cases b <;> rfl

/-- The homomorphism from the small amalgam to the large amalgam. -/
def matchedMap
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    PushoutI (smallEdge eA eB Z Q Delta hZ hQ) →*
      Amalgam.Push eA eB :=
  PushoutBaseChange.map
    (smallEdge eA eB Z Q Delta hZ hQ)
    (Amalgam.famHom eA eB)
    (edgeInclusion Delta) (factorInclusion Z Q)
    (factorInclusion_commutes eA eB Z Q Delta hZ hQ)

/-- Left and right factor maps, with the dependent `Bool` family hidden behind
ordinary homomorphism types. -/
def smallInZ (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    ↥Z →* PushoutI (smallEdge eA eB Z Q Delta hZ hQ) :=
  PushoutI.of (φ := smallEdge eA eB Z Q Delta hZ hQ) false

def smallInQ (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    ↥Q →* PushoutI (smallEdge eA eB Z Q Delta hZ hQ) :=
  PushoutI.of (φ := smallEdge eA eB Z Q Delta hZ hQ) true

def bigInA : A →* Amalgam.Push eA eB :=
  PushoutI.of (φ := Amalgam.famHom eA eB) false

def bigInB : B →* Amalgam.Push eA eB :=
  PushoutI.of (φ := Amalgam.famHom eA eB) true

@[simp] theorem matchedMap_smallInZ
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) (z : ↥Z) :
    matchedMap eA eB Z Q Delta hZ hQ (smallInZ eA eB Z Q Delta hZ hQ z) =
      bigInA eA eB (z : A) := by
  exact PushoutBaseChange.map_of
    (smallEdge eA eB Z Q Delta hZ hQ)
    (Amalgam.famHom eA eB) (edgeInclusion Delta)
    (factorInclusion Z Q)
    (factorInclusion_commutes eA eB Z Q Delta hZ hQ) false z

@[simp] theorem matchedMap_smallInQ
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) (q : ↥Q) :
    matchedMap eA eB Z Q Delta hZ hQ (smallInQ eA eB Z Q Delta hZ hQ q) =
      bigInB eA eB (q : B) := by
  exact PushoutBaseChange.map_of
    (smallEdge eA eB Z Q Delta hZ hQ)
    (Amalgam.famHom eA eB) (edgeInclusion Delta)
    (factorInclusion Z Q)
    (factorInclusion_commutes eA eB Z Q Delta hZ hQ) true q

theorem smallEdge_injective
    (heA : Function.Injective eA) (heB : Function.Injective eB)
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    ∀ b, Function.Injective (smallEdge eA eB Z Q Delta hZ hQ b) := by
  intro b
  cases b with
  | false =>
      intro x y hxy
      apply Subtype.ext
      apply heA
      exact congrArg Subtype.val hxy
  | true =>
      intro x y hxy
      apply Subtype.ext
      apply heB
      exact congrArg Subtype.val hxy

theorem factorInclusion_reflects_range
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    ∀ b g, factorInclusion Z Q b g ∈ (Amalgam.famHom eA eB b).range →
      g ∈ (smallEdge eA eB Z Q Delta hZ hQ b).range := by
  intro b
  cases b with
  | false =>
      intro z hz
      change ↥Z at z
      obtain ⟨m, hm⟩ := hz
      change eA m = (z : A) at hm
      have hmDelta : m ∈ Delta := by
        rw [← hZ]
        change eA m ∈ Z
        rw [hm]
        exact z.property
      refine ⟨⟨m, hmDelta⟩, ?_⟩
      exact Subtype.ext hm
  | true =>
      intro q hq
      change ↥Q at q
      obtain ⟨m, hm⟩ := hq
      change eB m = (q : B) at hm
      have hmDelta : m ∈ Delta := by
        rw [← hQ]
        change eB m ∈ Q
        rw [hm]
        exact q.property
      refine ⟨⟨m, hmDelta⟩, ?_⟩
      exact Subtype.ext hm

/-- **Matched sub-amalgam embedding.**  Exact agreement of the two edge
intersections makes `Z *_Delta Q → A *_M B` injective. -/
theorem matchedMap_injective
    (heA : Function.Injective eA) (heB : Function.Injective eB)
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    Function.Injective (matchedMap eA eB Z Q Delta hZ hQ) := by
  apply PushoutBaseChange.map_injective_of_reflects_range
  · exact smallEdge_injective eA eB Z Q Delta heA heB hZ hQ
  · exact Amalgam.famHom_injective eA eB heA heB
  · exact Subtype.val_injective
  · intro b
    cases b <;> exact Subtype.val_injective
  · exact factorInclusion_reflects_range eA eB Z Q Delta hZ hQ

/-- The generating set in the large amalgam: the left copy of `Z` and the
right copy of `Q`. -/
def generatorSet : Set (Amalgam.Push eA eB) :=
  (bigInA eA eB '' (Z : Set A)) ∪ (bigInB eA eB '' (Q : Set B))

/-- The range of the small amalgam is exactly the subgroup generated by the
two matched factor subgroups. -/
theorem matchedMap_range_eq_closure
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    (matchedMap eA eB Z Q Delta hZ hQ).range =
      Subgroup.closure (generatorSet eA eB Z Q) := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using PushoutI.induction_on with
    | of b g =>
        cases b with
        | false =>
            change ↥Z at g
            exact Subgroup.subset_closure
              (Or.inl ⟨(g : A), g.property, by
                exact (matchedMap_smallInZ eA eB Z Q Delta hZ hQ g).symm⟩)
        | true =>
            change ↥Q at g
            exact Subgroup.subset_closure
              (Or.inr ⟨(g : B), g.property, by
                exact (matchedMap_smallInQ eA eB Z Q Delta hZ hQ g).symm⟩)
    | base d =>
        have hfactor :
            PushoutI.base (smallEdge eA eB Z Q Delta hZ hQ) d =
              smallInZ eA eB Z Q Delta hZ hQ
                (edgeToZ eA Z Delta hZ d) :=
          (PushoutI.of_apply_eq_base
            (smallEdge eA eB Z Q Delta hZ hQ) false d).symm
        rw [hfactor]
        exact Subgroup.subset_closure
          (Or.inl ⟨eA d, (edgeToZ eA Z Delta hZ d).property,
            by
              exact (matchedMap_smallInZ eA eB Z Q Delta hZ hQ
                (edgeToZ eA Z Delta hZ d)).symm⟩)
    | mul x y hx hy =>
        rw [map_mul]
        exact Subgroup.mul_mem _ hx hy
  · refine (Subgroup.closure_le _).mpr ?_
    rintro x (⟨z, hz, rfl⟩ | ⟨q, hq, rfl⟩)
    · let zs : ↥Z := ⟨z, hz⟩
      refine ⟨smallInZ eA eB Z Q Delta hZ hQ zs, ?_⟩
      exact matchedMap_smallInZ eA eB Z Q Delta hZ hQ zs
    · let qs : ↥Q := ⟨q, hq⟩
      refine ⟨smallInQ eA eB Z Q Delta hZ hQ qs, ?_⟩
      exact matchedMap_smallInQ eA eB Z Q Delta hZ hQ qs

/-! ## Normal-form factor reflection -/

/-- A nonempty reduced word whose first letter is not in the `i`-th factor
cannot represent an element of that factor.  This is the one-sided normal-form
statement needed below; prefixing by the inverse of a putative factor
representative produces a nonempty reduced word in the base. -/
theorem reduced_not_mem_factor_of_fstIdx_ne
    {ι : Type} {H : Type} {G : ι → Type}
    [Group H] [∀ i, Group (G i)]
    (φ : ∀ i, H →* G i) (hφ : ∀ i, Function.Injective (φ i))
    (i : ι) (w : Monoid.CoprodI.Word G)
    (hw : PushoutI.Reduced φ w) (hne : w.toList ≠ [])
    (hfst : w.fstIdx ≠ some i) :
    PushoutI.ofCoprodI w.prod ∉ (PushoutI.of (φ := φ) i).range := by
  classical
  intro hmem
  obtain ⟨g, hg⟩ := hmem
  by_cases hgr : g ∈ (φ i).range
  · have hbase : PushoutI.ofCoprodI w.prod ∈ (PushoutI.base φ).range := by
      obtain ⟨h, hh⟩ := hgr
      refine ⟨h, ?_⟩
      rw [← hg, ← hh]
      exact (PushoutI.of_apply_eq_base φ i h).symm
    have hempty := hw.eq_empty_of_mem_range hφ hbase
    apply hne
    have hlist := congrArg Monoid.CoprodI.Word.toList hempty
    simpa [Monoid.CoprodI.Word.empty] using hlist
  · have hginv : g⁻¹ ≠ 1 := by
      intro hg1
      apply hgr
      have : g = 1 := inv_eq_one.mp hg1
      rw [this]
      exact Subgroup.one_mem _
    let v : Monoid.CoprodI.Word G :=
      Monoid.CoprodI.Word.cons g⁻¹ w hfst hginv
    have hvred : PushoutI.Reduced φ v := by
      rintro ⟨j, x⟩ hx
      change ⟨j, x⟩ ∈ (⟨i, g⁻¹⟩ :: w.toList) at hx
      rcases List.mem_cons.mp hx with hx | hx
      · cases hx
        intro hinv
        apply hgr
        obtain ⟨h, hh⟩ := hinv
        refine ⟨h⁻¹, ?_⟩
        simpa using congrArg Inv.inv hh
      · exact hw ⟨j, x⟩ hx
    have hvone : (PushoutI.ofCoprodI v.prod : PushoutI φ) = 1 := by
      rw [Monoid.CoprodI.Word.prod_cons, map_mul, PushoutI.ofCoprodI_of,
        ← hg]
      simp
    have hvbase : (PushoutI.ofCoprodI v.prod : PushoutI φ) ∈
        (PushoutI.base φ).range := by
      rw [hvone]
      exact Subgroup.one_mem _
    have hempty := hvred.eq_empty_of_mem_range hφ hvbase
    have hlist := congrArg Monoid.CoprodI.Word.toList hempty
    simp [v, Monoid.CoprodI.Word.cons, Monoid.CoprodI.Word.empty] at hlist

/-- A reduced word representing an element of the `i`-th factor has at most
one syllable, and a nonempty such word starts in the `i`-th factor. -/
theorem reduced_factor_shape
    {ι : Type} {H : Type} {G : ι → Type}
    [Group H] [∀ i, Group (G i)]
    (φ : ∀ i, H →* G i) (hφ : ∀ i, Function.Injective (φ i))
    (i : ι) (w : Monoid.CoprodI.Word G)
    (hw : PushoutI.Reduced φ w)
    (hmem : PushoutI.ofCoprodI w.prod ∈ (PushoutI.of (φ := φ) i).range) :
    w.toList.tail = [] ∧ (w.toList ≠ [] → w.fstIdx = some i) := by
  classical
  by_cases hnil : w.toList = []
  · exact ⟨by simp [hnil], fun h ↦ (h hnil).elim⟩
  obtain ⟨j, g, w', hidx, hg, hwcons⟩ :=
    PushoutITorsionFree.exists_cons w hnil
  subst w
  have htail : w'.toList = [] := by
    by_contra hne
    by_cases hji : j = i
    · subst j
      obtain ⟨a, ha⟩ := hmem
      have htailMem : (PushoutI.ofCoprodI w'.prod : PushoutI φ) ∈
          (PushoutI.of (φ := φ) i).range := by
        refine ⟨g⁻¹ * a, ?_⟩
        calc
          PushoutI.of (φ := φ) i (g⁻¹ * a) =
              (PushoutI.of (φ := φ) i g)⁻¹ *
                PushoutI.of (φ := φ) i a := by simp
          _ = (PushoutI.of (φ := φ) i g)⁻¹ *
                PushoutI.ofCoprodI
                  (Monoid.CoprodI.Word.cons g w' hidx hg).prod :=
              congrArg (fun z ↦ (PushoutI.of (φ := φ) i g)⁻¹ * z) ha
          _ = PushoutI.ofCoprodI w'.prod := by
              rw [Monoid.CoprodI.Word.prod_cons, map_mul,
                PushoutI.ofCoprodI_of]
              simp
      exact reduced_not_mem_factor_of_fstIdx_ne φ hφ i w'
        (fun l hl ↦ hw l (List.mem_cons_of_mem _ hl)) hne hidx htailMem
    · have hfst :
          (Monoid.CoprodI.Word.cons g w' hidx hg).fstIdx ≠ some i := by
        simp only [Monoid.CoprodI.Word.fstIdx, Monoid.CoprodI.Word.cons,
          List.head?_cons, Option.map_some]
        exact fun h ↦ hji (Option.some.inj h)
      exact reduced_not_mem_factor_of_fstIdx_ne φ hφ i
        (Monoid.CoprodI.Word.cons g w' hidx hg) hw (by simp) hfst hmem
  constructor
  · simp [Monoid.CoprodI.Word.cons, htail]
  · intro _
    by_contra hne
    exact reduced_not_mem_factor_of_fstIdx_ne φ hφ i
      (Monoid.CoprodI.Word.cons g w' hidx hg) hw (by simp) hne hmem

/-- **Factor-range reflection for the embedded small amalgam.**  If an element
of the small amalgam maps into one chosen factor of the large amalgam, it was
already in the corresponding small factor. -/
theorem matchedMap_reflects_factor_range
    (heA : Function.Injective eA) (heB : Function.Injective eB)
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    ∀ b x, matchedMap eA eB Z Q Delta hZ hQ x ∈
        (PushoutI.of (φ := Amalgam.famHom eA eB) b).range →
      x ∈ (PushoutI.of
        (φ := smallEdge eA eB Z Q Delta hZ hQ) b).range := by
  classical
  intro b x hx
  obtain ⟨d⟩ := PushoutI.NormalWord.transversal_nonempty
    (smallEdge eA eB Z Q Delta hZ hQ)
    (smallEdge_injective eA eB Z Q Delta heA heB hZ hQ)
  let w : PushoutI.NormalWord d := PushoutI.NormalWord.equiv x
  have hxprod : w.prod = x :=
    (PushoutI.NormalWord.equiv (d := d)).symm_apply_apply x
  let wm := PushoutEmbedding.wordMap (factorInclusion Z Q)
    (fun i ↦ by cases i <;> exact Subtype.val_injective) w.toWord
  have hredSource : PushoutI.Reduced
      (smallEdge eA eB Z Q Delta hZ hQ) w.toWord :=
    PushoutEmbedding.normalWord_reduced _ d w
  have hredTarget : PushoutI.Reduced (Amalgam.famHom eA eB) wm := by
    intro l hl
    obtain ⟨l', hl', heq⟩ := List.mem_map.mp hl
    cases heq
    exact fun hrange ↦ hredSource l' hl'
      (factorInclusion_reflects_range eA eB Z Q Delta hZ hQ l'.1 l'.2 hrange)
  have hprodImage :
      matchedMap eA eB Z Q Delta hZ hQ w.prod =
        PushoutI.base (Amalgam.famHom eA eB) (edgeInclusion Delta w.head) *
          PushoutI.ofCoprodI wm.prod := by
    rw [PushoutI.NormalWord.prod, map_mul, matchedMap,
      PushoutBaseChange.map_base, PushoutBaseChange.map_ofCoprodI_prod]
  have hbaseFactor :
      PushoutI.base (Amalgam.famHom eA eB) (edgeInclusion Delta w.head) ∈
        (PushoutI.of (φ := Amalgam.famHom eA eB) b).range := by
    refine ⟨Amalgam.famHom eA eB b (edgeInclusion Delta w.head), ?_⟩
    exact PushoutI.of_apply_eq_base _ b (edgeInclusion Delta w.head)
  have hwordFactor : PushoutI.ofCoprodI wm.prod ∈
      (PushoutI.of (φ := Amalgam.famHom eA eB) b).range := by
    have heq : PushoutI.ofCoprodI wm.prod =
        (PushoutI.base (Amalgam.famHom eA eB) (edgeInclusion Delta w.head))⁻¹ *
          matchedMap eA eB Z Q Delta hZ hQ x := by
      rw [← hxprod, hprodImage]
      simp
    rw [heq]
    exact (PushoutI.of (φ := Amalgam.famHom eA eB) b).range.mul_mem
      ((PushoutI.of (φ := Amalgam.famHom eA eB) b).range.inv_mem hbaseFactor) hx
  obtain ⟨hmtail, hmfst⟩ := reduced_factor_shape
    (Amalgam.famHom eA eB)
    (Amalgam.famHom_injective eA eB heA heB) b wm hredTarget hwordFactor
  cases hlist : w.toWord.toList with
  | nil =>
      refine ⟨smallEdge eA eB Z Q Delta hZ hQ b w.head, ?_⟩
      calc
        PushoutI.of (φ := smallEdge eA eB Z Q Delta hZ hQ) b
            (smallEdge eA eB Z Q Delta hZ hQ b w.head) =
            PushoutI.base (smallEdge eA eB Z Q Delta hZ hQ) w.head :=
          PushoutI.of_apply_eq_base _ b w.head
        _ = w.prod := by
          rw [PushoutI.NormalWord.prod]
          have hwordOne : w.toWord.prod = 1 := by
            simp [Monoid.CoprodI.Word.prod, hlist]
          rw [hwordOne, map_one, mul_one]
        _ = x := hxprod

  | cons a rest =>
      have hrest : rest = [] := by
        have ht := hmtail
        simp only [wm, PushoutEmbedding.wordMap_toList, hlist,
          List.map_cons, List.tail_cons] at ht
        cases rest with
        | nil => rfl
        | cons c cs => simp at ht
      subst rest
      rcases a with ⟨j, g⟩
      have hwmne : wm.toList ≠ [] := by
        simp [wm, PushoutEmbedding.wordMap, hlist]
      have hwmidx := hmfst hwmne
      have hji : j = b := by
        simpa [wm, PushoutEmbedding.wordMap, hlist,
          Monoid.CoprodI.Word.fstIdx] using hwmidx
      subst j
      refine ⟨smallEdge eA eB Z Q Delta hZ hQ b w.head * g, ?_⟩
      calc
        PushoutI.of (φ := smallEdge eA eB Z Q Delta hZ hQ) b
            (smallEdge eA eB Z Q Delta hZ hQ b w.head * g) =
            PushoutI.base (smallEdge eA eB Z Q Delta hZ hQ) w.head *
              PushoutI.of (φ := smallEdge eA eB Z Q Delta hZ hQ) b g := by
          rw [map_mul, PushoutI.of_apply_eq_base]
        _ = w.prod := by
          rw [PushoutI.NormalWord.prod]
          simp [Monoid.CoprodI.Word.prod, hlist]
        _ = x := hxprod

/-- The subgroup generated by the two matched factor subgroups meets the left
large factor in exactly the embedded left small subgroup. -/
theorem generatorClosure_inf_leftRange
    (heA : Function.Injective eA) (heB : Function.Injective eB)
    (hZ : Z.comap eA = Delta) (hQ : Q.comap eB = Delta) :
    Subgroup.closure (generatorSet eA eB Z Q) ⊓ (bigInA eA eB).range =
      Z.map (bigInA eA eB) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxGen, hxA⟩ := Subgroup.mem_inf.mp hx
    rw [← matchedMap_range_eq_closure eA eB Z Q Delta hZ hQ] at hxGen
    obtain ⟨y, hy⟩ := hxGen
    have hyA : matchedMap eA eB Z Q Delta hZ hQ y ∈
        (bigInA eA eB).range := by
      rwa [hy]
    obtain ⟨z, hz⟩ := matchedMap_reflects_factor_range
      eA eB Z Q Delta heA heB hZ hQ false y hyA
    change ↥Z at z
    refine Subgroup.mem_map.mpr ⟨(z : A), z.property, ?_⟩
    rw [← hy, ← hz]
    exact matchedMap_smallInZ eA eB Z Q Delta hZ hQ z
  · rintro x ⟨z, hz, rfl⟩
    exact Subgroup.mem_inf.mpr ⟨
      Subgroup.subset_closure (Or.inl ⟨z, hz, rfl⟩),
      ⟨z, rfl⟩⟩

end MatchedSubgroupAmalgam
end Higman
end GroupApproximation
