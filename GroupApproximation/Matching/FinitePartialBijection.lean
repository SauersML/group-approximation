import GroupApproximation.Sofic.Sofic
import Mathlib.Logic.Equiv.Fintype

/-!
# Partial bijections of finite models

Cluster arrows are almost equivariant partial bijections between expander
components.  This file provides their concrete finite carrier, inverse,
graph, extension, and defect sets.  No quotient or asymptotic premise is
involved here.
-/

namespace GroupApproximation

/-- A bijection between two explicitly specified finite subsets. -/
structure FinitePartialBijection (Y Z : FiniteModel) where
  source : Finset Y
  target : Finset Z
  equiv : source ≃ target

namespace FinitePartialBijection

variable {Y Z W V : FiniteModel}

/-- Value of a partial bijection at a point with a source-membership proof. -/
def apply (b : FinitePartialBijection Y Z) (y : Y) (hy : y ∈ b.source) : Z :=
  (b.equiv ⟨y, hy⟩).1

/-- Two partial bijections are equal when their source, target, and values
agree.  Proofs of membership carry no additional data. -/
@[ext (iff := false)] theorem ext {b c : FinitePartialBijection Y Z}
    (hsource : b.source = c.source) (htarget : b.target = c.target)
    (happly : ∀ y (hy : y ∈ b.source),
      b.apply y hy = c.apply y (hsource ▸ hy)) : b = c := by
  cases b with
  | mk bsource btarget bequiv =>
    cases c with
    | mk csource ctarget cequiv =>
      dsimp only at hsource htarget happly
      subst csource
      subst ctarget
      congr
      apply Equiv.ext
      intro y
      apply Subtype.ext
      exact happly y.1 y.2

/-- There are only finitely many partial bijections between two finite
models.  Exposing this instance lets quotient cluster presentations inherit
finite Hom-sets automatically. -/
noncomputable instance finite : Finite (FinitePartialBijection Y Z) := by
  classical
  let encode : FinitePartialBijection Y Z →
      Finset Y × Finset Z × Finset (Y × Z) := fun b ↦
    (b.source, b.target, Finset.univ.filter fun p ↦
      ∃ hy : p.1 ∈ b.source, b.apply p.1 hy = p.2)
  apply Finite.of_injective encode
  intro b c hbc
  have hs : b.source = c.source := congrArg (fun p ↦ p.1) hbc
  have ht : b.target = c.target := congrArg (fun p ↦ p.2.1) hbc
  apply ext hs ht
  intro y hy
  have hyc : y ∈ c.source := hs ▸ hy
  have hg := congrArg (fun p ↦ p.2.2) hbc
  have hbmem : (y, b.apply y hy) ∈
      (encode b).2.2 := by
    simp [encode, hy]
  have hcmem : (y, b.apply y hy) ∈ (encode c).2.2 := hg ▸ hbmem
  simp only [encode, Finset.mem_filter, Finset.mem_univ, true_and] at hcmem
  obtain ⟨hyc', hval⟩ := hcmem
  simpa only [proof_irrel_heq] using hval.symm

theorem apply_mem_target (b : FinitePartialBijection Y Z)
    (y : Y) (hy : y ∈ b.source) : b.apply y hy ∈ b.target :=
  (b.equiv ⟨y, hy⟩).2

theorem apply_injective (b : FinitePartialBijection Y Z)
    {x y : Y} (hx : x ∈ b.source) (hy : y ∈ b.source)
    (hxy : b.apply x hx = b.apply y hy) : x = y := by
  have hsub : (⟨x, hx⟩ : b.source) = ⟨y, hy⟩ := by
    apply b.equiv.injective
    exact Subtype.ext hxy
  exact congrArg Subtype.val hsub

/-- The full identity partial bijection. -/
def refl (Y : FiniteModel) : FinitePartialBijection Y Y where
  source := Finset.univ
  target := Finset.univ
  equiv :=
    { toFun := fun y ↦ ⟨y.1, Finset.mem_univ _⟩
      invFun := fun y ↦ ⟨y.1, Finset.mem_univ _⟩
      left_inv := fun y ↦ by cases y; rfl
      right_inv := fun y ↦ by cases y; rfl }

@[simp] theorem refl_apply (y : Y) (hy : y ∈ (refl Y).source) :
    (refl Y).apply y hy = y := rfl

/-- Identity restricted to an explicitly chosen finite subset. -/
def reflOn (s : Finset Y) : FinitePartialBijection Y Y where
  source := s
  target := s
  equiv := Equiv.refl s

@[simp] theorem reflOn_source (s : Finset Y) : (reflOn s).source = s := rfl

@[simp] theorem reflOn_target (s : Finset Y) : (reflOn s).target = s := rfl

@[simp] theorem reflOn_apply (s : Finset Y) (y : Y) (hy : y ∈ s) :
    (reflOn s).apply y hy = y := rfl

/-- Reverse a finite partial bijection. -/
def symm (b : FinitePartialBijection Y Z) : FinitePartialBijection Z Y where
  source := b.target
  target := b.source
  equiv := b.equiv.symm

@[simp] theorem symm_source (b : FinitePartialBijection Y Z) :
    b.symm.source = b.target := rfl

@[simp] theorem symm_target (b : FinitePartialBijection Y Z) :
    b.symm.target = b.source := rfl

@[simp] theorem symm_symm (b : FinitePartialBijection Y Z) : b.symm.symm = b := by
  cases b
  rfl

@[simp] theorem symm_refl_apply (y : Y) (hy : y ∈ (refl Y).symm.source) :
    (refl Y).symm.apply y hy = y := rfl

@[simp] theorem symm_apply_apply (b : FinitePartialBijection Y Z)
    (y : Y) (hy : y ∈ b.source) :
    b.symm.apply (b.apply y hy) (b.apply_mem_target y hy) = y := by
  exact congrArg Subtype.val (b.equiv.symm_apply_apply ⟨y, hy⟩)

@[simp] theorem apply_symm_apply (b : FinitePartialBijection Y Z)
    (z : Z) (hz : z ∈ b.target) :
    b.apply (b.symm.apply z hz) (b.symm.apply_mem_target z hz) = z := by
  exact congrArg Subtype.val (b.equiv.apply_symm_apply ⟨z, hz⟩)

/-- The source and pointwise values determine a partial bijection; its target
is necessarily the image of its source. -/
theorem ext_source {b c : FinitePartialBijection Y Z}
    (hsource : b.source = c.source)
    (happly : ∀ y (hy : y ∈ b.source),
      b.apply y hy = c.apply y (hsource ▸ hy)) : b = c := by
  have htarget : b.target = c.target := by
    ext z
    constructor
    · intro hz
      let y := b.symm.apply z hz
      have hyb : y ∈ b.source := b.symm.apply_mem_target z hz
      have hyc : y ∈ c.source := hsource ▸ hyb
      have hmem : c.apply y hyc ∈ c.target := c.apply_mem_target y hyc
      have hval : b.apply y hyb = c.apply y hyc := by
        simpa only [proof_irrel_heq] using happly y hyb
      rw [← b.apply_symm_apply z hz, hval]
      exact hmem
    · intro hz
      let y := c.symm.apply z hz
      have hyc : y ∈ c.source := c.symm.apply_mem_target z hz
      have hyb : y ∈ b.source := hsource.symm ▸ hyc
      have hmem : b.apply y hyb ∈ b.target := b.apply_mem_target y hyb
      have hval : b.apply y hyb = c.apply y hyc := by
        simpa only [proof_irrel_heq] using happly y hyb
      rw [← c.apply_symm_apply z hz, ← hval]
      exact hmem
  exact ext hsource htarget happly

/-- A source point at which `b` may be followed by `c`. -/
def ComposableAt (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) (y : Y) : Prop :=
  ∃ hy : y ∈ b.source, b.apply y hy ∈ c.source

/-- A target point having a preimage through both `b` and `c`. -/
def BackComposableAt (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) (w : W) : Prop :=
  ∃ hw : w ∈ c.target, c.symm.apply w hw ∈ b.target

/-- Composition of partial bijections, restricted to the points at which the
first map lands in the source of the second. -/
noncomputable def trans (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) : FinitePartialBijection Y W := by
  classical
  exact
   { source := b.source.filter (ComposableAt b c)
     target := c.target.filter (BackComposableAt b c)
     equiv :=
    { toFun := fun y ↦ by
        have hyb : y.1 ∈ b.source := (Finset.mem_filter.mp y.2).1
        have hyc : b.apply y.1 hyb ∈ c.source := by
          obtain ⟨hyb', hyc⟩ := (Finset.mem_filter.mp y.2).2
          simpa only [proof_irrel_heq] using hyc
        refine ⟨c.apply (b.apply y.1 hyb) hyc, ?_⟩
        rw [Finset.mem_filter]
        refine ⟨c.apply_mem_target _ _, ?_⟩
        refine ⟨c.apply_mem_target _ _, ?_⟩
        simpa only [symm_apply_apply] using b.apply_mem_target y.1 hyb
      invFun := fun w ↦ by
        have hwc : w.1 ∈ c.target := (Finset.mem_filter.mp w.2).1
        have hwb : c.symm.apply w.1 hwc ∈ b.target := by
          obtain ⟨hwc', hwb⟩ := (Finset.mem_filter.mp w.2).2
          simpa only [proof_irrel_heq] using hwb
        refine ⟨b.symm.apply (c.symm.apply w.1 hwc) hwb, ?_⟩
        rw [Finset.mem_filter]
        refine ⟨b.symm.apply_mem_target _ _, ?_⟩
        refine ⟨b.symm.apply_mem_target _ _, ?_⟩
        simpa only [symm_target, apply_symm_apply] using
          c.symm.apply_mem_target w.1 hwc
      left_inv := fun y ↦ by
        apply Subtype.ext
        simp
      right_inv := fun w ↦ by
        apply Subtype.ext
        simp } }

@[simp] theorem mem_trans_source (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) (y : Y) :
    y ∈ (b.trans c).source ↔
      ∃ hy : y ∈ b.source, b.apply y hy ∈ c.source := by
  classical
  simp only [trans, Finset.mem_filter, ComposableAt]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨hy, h⟩
    exact ⟨hy, hy, h⟩

@[simp] theorem mem_trans_target (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) (w : W) :
    w ∈ (b.trans c).target ↔
      ∃ hw : w ∈ c.target, c.symm.apply w hw ∈ b.target := by
  classical
  simp only [trans, Finset.mem_filter, BackComposableAt]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · rintro ⟨hw, h⟩
    exact ⟨hw, hw, h⟩

@[simp] theorem trans_apply (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) (y : Y)
    (hy : y ∈ (b.trans c).source) :
    (b.trans c).apply y hy =
      c.apply (b.apply y ((b.mem_trans_source c y).mp hy).choose)
        ((b.mem_trans_source c y).mp hy).choose_spec := rfl

@[simp] theorem refl_trans (b : FinitePartialBijection Y Z) :
    (refl Y).trans b = b := by
  classical
  have hs : ((refl Y).trans b).source = b.source := by
    ext y
    constructor
    · intro hy
      obtain ⟨_, h⟩ := ((refl Y).mem_trans_source b y).mp hy
      simpa using h
    · intro hy
      exact ((refl Y).mem_trans_source b y).mpr
        ⟨Finset.mem_univ _, by simpa using hy⟩
  have ht : ((refl Y).trans b).target = b.target := by
    ext z
    constructor
    · intro hz
      exact (((refl Y).mem_trans_target b z).mp hz).choose
    · intro hz
      exact ((refl Y).mem_trans_target b z).mpr
        ⟨hz, Finset.mem_univ _⟩
  exact FinitePartialBijection.ext hs ht (by
    intro y hy
    simp)

@[simp] theorem trans_refl (b : FinitePartialBijection Y Z) :
    b.trans (refl Z) = b := by
  classical
  have hs : (b.trans (refl Z)).source = b.source := by
    ext y
    constructor
    · intro hy
      exact ((b.mem_trans_source (refl Z) y).mp hy).choose
    · intro hy
      exact (b.mem_trans_source (refl Z) y).mpr
        ⟨hy, Finset.mem_univ _⟩
  have ht : (b.trans (refl Z)).target = b.target := by
    ext z
    constructor
    · intro hz
      obtain ⟨_, h⟩ := (b.mem_trans_target (refl Z) z).mp hz
      simpa using h
    · intro hz
      exact (b.mem_trans_target (refl Z) z).mpr
        ⟨Finset.mem_univ _, by simpa using hz⟩
  exact FinitePartialBijection.ext hs ht (by
    intro y hy
    simp)

/-- Composition of finite partial bijections is associative. -/
theorem trans_assoc (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) (d : FinitePartialBijection W V) :
    (b.trans c).trans d = b.trans (c.trans d) := by
  classical
  have hs : ((b.trans c).trans d).source =
      (b.trans (c.trans d)).source := by
    ext y
    constructor
    · intro hy
      obtain ⟨hybc, hyd⟩ := ((b.trans c).mem_trans_source d y).mp hy
      obtain ⟨hyb, hyc⟩ := (b.mem_trans_source c y).mp hybc
      apply (b.mem_trans_source (c.trans d) y).mpr
      refine ⟨hyb, (c.mem_trans_source d (b.apply y hyb)).mpr ?_⟩
      refine ⟨hyc, ?_⟩
      simpa only [trans_apply, proof_irrel_heq] using hyd
    · intro hy
      obtain ⟨hyb, hycd⟩ := (b.mem_trans_source (c.trans d) y).mp hy
      obtain ⟨hyc, hyd⟩ :=
        (c.mem_trans_source d (b.apply y hyb)).mp hycd
      apply ((b.trans c).mem_trans_source d y).mpr
      have hybc : y ∈ (b.trans c).source :=
        (b.mem_trans_source c y).mpr ⟨hyb, hyc⟩
      refine ⟨hybc, ?_⟩
      simpa only [trans_apply, proof_irrel_heq] using hyd
  exact ext_source hs (by
    intro y hy
    simp only [trans_apply])

/-- Reversing a composite reverses the order of its factors. -/
theorem symm_trans (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) :
    (b.trans c).symm = c.symm.trans b.symm := by
  classical
  have hs : (b.trans c).symm.source = (c.symm.trans b.symm).source := by
    ext w
    rw [symm_source, b.mem_trans_target c w]
    rw [c.symm.mem_trans_source b.symm w]
    rfl
  exact ext_source hs (by
    intro w hw
    rfl)

/-- Composing an arrow with its reverse is the identity on its source. -/
theorem trans_symm (b : FinitePartialBijection Y Z) :
    b.trans b.symm = reflOn b.source := by
  classical
  have hs : (b.trans b.symm).source = (reflOn b.source).source := by
    ext y
    constructor
    · intro hy
      exact (b.mem_trans_source b.symm y).mp hy |>.choose
    · intro hy
      apply (b.mem_trans_source b.symm y).mpr
      exact ⟨hy, b.apply_mem_target y hy⟩
  exact ext_source hs (by
    intro y hy
    simp only [trans_apply, symm_apply_apply, reflOn_apply])

/-- Composing the reverse with the arrow is the identity on its target. -/
theorem symm_trans_self (b : FinitePartialBijection Y Z) :
    b.symm.trans b = reflOn b.target := by
  simpa only [symm_source, symm_symm] using trans_symm b.symm

/-- Images under `b` of the source points discarded when composing with
`c`.  Injectivity of `b` makes this set have exactly the discarded-source
cardinality. -/
noncomputable def droppedSourceImage (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) : Finset Z :=
  (b.source \ (b.trans c).source).attach.map
    ⟨fun y ↦ b.apply y.1 (Finset.mem_sdiff.mp y.2).1, by
      intro x y h
      apply Subtype.ext
      exact b.apply_injective (Finset.mem_sdiff.mp x.2).1
        (Finset.mem_sdiff.mp y.2).1 h⟩

@[simp] theorem card_droppedSourceImage (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) :
    (b.droppedSourceImage c).card =
      (b.source \ (b.trans c).source).card := by
  classical
  simp [droppedSourceImage]

/-- Every discarded source point maps outside the next source. -/
theorem droppedSourceImage_subset (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) :
    b.droppedSourceImage c ⊆ Finset.univ \ c.source := by
  classical
  intro z hz
  rw [droppedSourceImage, Finset.mem_map] at hz
  obtain ⟨y, _, rfl⟩ := hz
  rw [Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hc
  exact (Finset.mem_sdiff.mp y.2).2
    ((b.mem_trans_source c y.1).mpr
      ⟨(Finset.mem_sdiff.mp y.2).1, hc⟩)

/-- Graph of the partial bijection. -/
noncomputable def graph (b : FinitePartialBijection Y Z) : Finset (Y × Z) :=
  b.source.attach.map
    ⟨fun y ↦ (y.1, b.apply y.1 y.2), by
      intro x y h
      exact Subtype.ext (congrArg Prod.fst h)⟩

@[simp] theorem mem_graph (b : FinitePartialBijection Y Z) (y : Y) (z : Z) :
    (y, z) ∈ b.graph ↔ ∃ hy : y ∈ b.source, b.apply y hy = z := by
  classical
  constructor
  · intro h
    rw [graph, Finset.mem_map] at h
    obtain ⟨x, hx, hval⟩ := h
    have hxy : x.1 = y := congrArg Prod.fst hval
    subst y
    refine ⟨x.2, ?_⟩
    exact congrArg Prod.snd hval
  · rintro ⟨hy, rfl⟩
    rw [graph, Finset.mem_map]
    exact ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩

@[simp] theorem card_graph (b : FinitePartialBijection Y Z) :
    b.graph.card = b.source.card := by
  simp [graph]

theorem card_source_eq_card_target (b : FinitePartialBijection Y Z) :
    b.source.card = b.target.card := by
  simpa using Fintype.card_congr b.equiv

/-- Every partial permutation of one finite model extends to a permutation of
the whole model. -/
theorem exists_extension (b : FinitePartialBijection Y Y) :
    ∃ p : Equiv.Perm Y, ∀ y (hy : y ∈ b.source), p y = b.apply y hy := by
  let inclusion : b.source → Y := Subtype.val
  let target : b.source → Y := fun y ↦ b.apply y.1 y.2
  have hi : Function.Injective inclusion := Subtype.val_injective
  have ht : Function.Injective target := by
    intro x y h
    apply Subtype.ext
    exact b.apply_injective x.2 y.2 h
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair inclusion target hi ht
  exact ⟨p, fun y hy ↦ hp ⟨y, hy⟩⟩

/-- Missing source mass. -/
def sourceDefect (b : FinitePartialBijection Y Z) : ℕ :=
  Fintype.card Y - b.source.card

/-- Missing range mass. -/
def targetDefect (b : FinitePartialBijection Y Z) : ℕ :=
  Fintype.card Z - b.target.card

/-- Transport only the target model of a finite partial bijection along an
equality.  Naming this transport keeps dependent casts out of later defect
calculations. -/
def castTarget {Z' : FiniteModel} (h : Z = Z')
    (b : FinitePartialBijection Y Z) : FinitePartialBijection Y Z' :=
  h ▸ b

@[simp] theorem castTarget_sourceDefect {Z' : FiniteModel} (h : Z = Z')
    (b : FinitePartialBijection Y Z) :
    (castTarget h b).sourceDefect = b.sourceDefect := by
  subst Z'
  rfl

@[simp] theorem castTarget_targetDefect {Z' : FiniteModel} (h : Z = Z')
    (b : FinitePartialBijection Y Z) :
    (castTarget h b).targetDefect = b.targetDefect := by
  subst Z'
  rfl

@[simp] theorem sourceDefect_symm (b : FinitePartialBijection Y Z) :
    b.symm.sourceDefect = b.targetDefect := rfl

@[simp] theorem targetDefect_symm (b : FinitePartialBijection Y Z) :
    b.symm.targetDefect = b.sourceDefect := rfl

/-- Composition loses at most the first missing source plus the second
missing source. -/
theorem sourceDefect_trans_le (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) :
    (b.trans c).sourceDefect ≤ b.sourceDefect + c.sourceDefect := by
  classical
  have hsub : (b.trans c).source ⊆ b.source := by
    intro y hy
    exact ((b.mem_trans_source c y).mp hy).choose
  have hdrop : (b.source \ (b.trans c).source).card =
      b.source.card - (b.trans c).source.card := by
    rw [Finset.card_sdiff]
    rw [Finset.inter_eq_left.mpr hsub]
  have hdrop_le : (b.source \ (b.trans c).source).card ≤
      Fintype.card Z - c.source.card := by
    rw [← b.card_droppedSourceImage c]
    calc
      (b.droppedSourceImage c).card ≤ (Finset.univ \ c.source).card :=
        Finset.card_le_card (b.droppedSourceImage_subset c)
      _ = Fintype.card Z - c.source.card := by
        rw [Finset.card_sdiff]
        simp
  have hbcard : b.source.card ≤ Fintype.card Y := Finset.card_le_univ _
  have htcard : (b.trans c).source.card ≤ b.source.card :=
    Finset.card_le_card hsub
  unfold sourceDefect
  omega

/-- Composition loses at most the second missing target plus the first
missing target. -/
theorem targetDefect_trans_le (b : FinitePartialBijection Y Z)
    (c : FinitePartialBijection Z W) :
    (b.trans c).targetDefect ≤ c.targetDefect + b.targetDefect := by
  rw [← sourceDefect_symm, symm_trans]
  exact sourceDefect_trans_le c.symm b.symm

/-- Source points at which two partial maps cannot be compared or disagree. -/
noncomputable def disagreement (b c : FinitePartialBijection Y Z) : Finset Y :=
  Finset.univ.filter fun y ↦
    ∀ hb : y ∈ b.source, ∀ hc : y ∈ c.source,
      b.apply y hb ≠ c.apply y hc

@[simp] theorem mem_disagreement (b c : FinitePartialBijection Y Z) (y : Y) :
    y ∈ b.disagreement c ↔
      ∀ hb : y ∈ b.source, ∀ hc : y ∈ c.source,
        b.apply y hb ≠ c.apply y hc := by
  classical
  simp [disagreement]

/-- Disagreement is symmetric, including at points missing from one of the
two domains. -/
theorem disagreement_comm (b c : FinitePartialBijection Y Z) :
    b.disagreement c = c.disagreement b := by
  classical
  ext y
  simp only [mem_disagreement]
  constructor
  · intro h hc hb
    exact (h hb hc).symm
  · intro h hb hc
    exact (h hc hb).symm

/-- Self-disagreement is exactly the complement of the source. -/
theorem disagreement_self (b : FinitePartialBijection Y Z) :
    b.disagreement b = Finset.univ \ b.source := by
  classical
  ext y
  simp only [mem_disagreement, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · intro h hy
    exact (h hy hy) rfl
  · intro hy hb
    exact (hy hb).elim

theorem disagreement_reflOn_refl (s : Finset Y) :
    (reflOn s).disagreement (refl Y) = Finset.univ \ s := by
  classical
  ext y
  simp only [mem_disagreement, Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · intro h hy
    exact h hy (Finset.mem_univ _) rfl
  · intro hy hs
    exact (hy hs).elim

/-- Pointwise triangle inclusion for disagreement sets. -/
theorem disagreement_subset_union (b c d : FinitePartialBijection Y Z) :
    b.disagreement d ⊆ b.disagreement c ∪ c.disagreement d := by
  classical
  intro y hyd
  by_contra hnot
  have hnbc : y ∉ b.disagreement c := by
    intro h
    exact hnot (Finset.mem_union_left _ h)
  have hncd : y ∉ c.disagreement d := by
    intro h
    exact hnot (Finset.mem_union_right _ h)
  rw [mem_disagreement] at hnbc hncd hyd
  push Not at hnbc hncd
  obtain ⟨hb, hc, hbc⟩ := hnbc
  obtain ⟨hc', hd, hcd⟩ := hncd
  apply hyd hb hd
  calc
    b.apply y hb = c.apply y hc := hbc
    _ = c.apply y hc' := by congr
    _ = d.apply y hd := hcd

/-- Cardinal triangle inequality for finite disagreement. -/
theorem card_disagreement_le (b c d : FinitePartialBijection Y Z) :
    (b.disagreement d).card ≤
      (b.disagreement c).card + (c.disagreement d).card := by
  calc
    (b.disagreement d).card ≤
        (b.disagreement c ∪ c.disagreement d).card :=
      Finset.card_le_card (disagreement_subset_union b c d)
    _ ≤ (b.disagreement c).card + (c.disagreement d).card :=
      Finset.card_union_le _ _

/-- Source points of `a` whose images lie in the disagreement of two possible
second arrows. -/
def PullsDisagreement (a : FinitePartialBijection Y Z)
    (b c : FinitePartialBijection Z W) (y : Y) : Prop :=
  ∃ ha : y ∈ a.source, a.apply y ha ∈ b.disagreement c

noncomputable def pulledDisagreement (a : FinitePartialBijection Y Z)
    (b c : FinitePartialBijection Z W) : Finset Y := by
  classical
  exact a.source.filter (PullsDisagreement a b c)

noncomputable def pulledDisagreementImage (a : FinitePartialBijection Y Z)
    (b c : FinitePartialBijection Z W) : Finset Z := by
  classical
  exact (a.pulledDisagreement b c).attach.map
    ⟨fun y ↦ a.apply y.1
        (Finset.mem_filter.mp (show y.1 ∈ a.source.filter
          (PullsDisagreement a b c) by
            simp only [pulledDisagreement]
            exact y.2)).1, by
      intro x y h
      apply Subtype.ext
      apply a.apply_injective
          (Finset.mem_filter.mp (show x.1 ∈ a.source.filter
            (PullsDisagreement a b c) by
              simp only [pulledDisagreement]
              exact x.2)).1
          (Finset.mem_filter.mp (show y.1 ∈ a.source.filter
            (PullsDisagreement a b c) by
              simp only [pulledDisagreement]
              exact y.2)).1
      exact h⟩

@[simp] theorem card_pulledDisagreementImage
    (a : FinitePartialBijection Y Z) (b c : FinitePartialBijection Z W) :
    (a.pulledDisagreementImage b c).card =
      (a.pulledDisagreement b c).card := by
  classical
  simp [pulledDisagreementImage]

theorem pulledDisagreementImage_subset
    (a : FinitePartialBijection Y Z) (b c : FinitePartialBijection Z W) :
    a.pulledDisagreementImage b c ⊆ b.disagreement c := by
  classical
  intro z hz
  rw [pulledDisagreementImage, Finset.mem_map] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  obtain ⟨ha, hdis⟩ := (Finset.mem_filter.mp y.2).2
  change a.apply y.1 _ ∈ b.disagreement c
  simpa only [proof_irrel_heq] using hdis

theorem card_pulledDisagreement_le
    (a : FinitePartialBijection Y Z) (b c : FinitePartialBijection Z W) :
    (a.pulledDisagreement b c).card ≤ (b.disagreement c).card := by
  rw [← a.card_pulledDisagreementImage b c]
  exact Finset.card_le_card (a.pulledDisagreementImage_subset b c)

/-- A disagreement between composites comes either from the first arrows or
from a second-arrow disagreement pulled back through the first arrow. -/
theorem disagreement_trans_subset
    (a a' : FinitePartialBijection Y Z)
    (b b' : FinitePartialBijection Z W) :
    (a.trans b).disagreement (a'.trans b') ⊆
      a.disagreement a' ∪ a.pulledDisagreement b b' := by
  classical
  intro y hy
  by_contra hnot
  have hnaa' : y ∉ a.disagreement a' := by
    intro h
    exact hnot (Finset.mem_union_left _ h)
  have hpull : y ∉ a.pulledDisagreement b b' := by
    intro h
    exact hnot (Finset.mem_union_right _ h)
  rw [mem_disagreement] at hnaa' hy
  push Not at hnaa'
  obtain ⟨ha, ha', haa'⟩ := hnaa'
  have hnotbb' : a.apply y ha ∉ b.disagreement b' := by
    intro h
    apply hpull
    rw [pulledDisagreement, Finset.mem_filter]
    exact ⟨ha, ha, h⟩
  rw [mem_disagreement] at hnotbb'
  push Not at hnotbb'
  obtain ⟨hb, hb', hbb'⟩ := hnotbb'
  have hleft : y ∈ (a.trans b).source :=
    (a.mem_trans_source b y).mpr ⟨ha, hb⟩
  have hb'' : a'.apply y ha' ∈ b'.source := by simpa [haa'] using hb'
  have hright : y ∈ (a'.trans b').source :=
    (a'.mem_trans_source b' y).mpr ⟨ha', hb''⟩
  apply hy hleft hright
  simp only [trans_apply]
  calc
    b.apply (a.apply y _) _ = b'.apply (a.apply y ha) hb' := hbb'
    _ = b'.apply (a'.apply y _) _ := by
      simp only [haa']

/-- Cardinal error bound showing that composition is Lipschitz for finite
partial disagreement. -/
theorem card_disagreement_trans_le
    (a a' : FinitePartialBijection Y Z)
    (b b' : FinitePartialBijection Z W) :
    ((a.trans b).disagreement (a'.trans b')).card ≤
      (a.disagreement a').card + (b.disagreement b').card := by
  calc
    ((a.trans b).disagreement (a'.trans b')).card ≤
        (a.disagreement a' ∪ a.pulledDisagreement b b').card :=
      Finset.card_le_card (disagreement_trans_subset a a' b b')
    _ ≤ (a.disagreement a').card + (a.pulledDisagreement b b').card :=
      Finset.card_union_le _ _
    _ ≤ (a.disagreement a').card + (b.disagreement b').card :=
      Nat.add_le_add_left (a.card_pulledDisagreement_le b b') _

/-- The cardinality of self-disagreement is the source defect. -/
@[simp] theorem card_disagreement_self (b : FinitePartialBijection Y Z) :
    (b.disagreement b).card = b.sourceDefect := by
  classical
  rw [disagreement_self, sourceDefect]
  rw [Finset.card_sdiff]
  simp

/-- Disagreement counted in both source and target coordinates.  This is the
inverse-invariant error used for quotient groupoid arrows. -/
noncomputable def twoSidedDisagreement (b c : FinitePartialBijection Y Z) : ℕ :=
  (b.disagreement c).card + (b.symm.disagreement c.symm).card

@[simp] theorem twoSidedDisagreement_self (b : FinitePartialBijection Y Z) :
    b.twoSidedDisagreement b = b.sourceDefect + b.targetDefect := by
  rw [twoSidedDisagreement, card_disagreement_self,
    card_disagreement_self, sourceDefect_symm]

theorem twoSidedDisagreement_reflOn_refl (s : Finset Y) :
    (reflOn s).twoSidedDisagreement (refl Y) =
      2 * (Fintype.card Y - s.card) := by
  rw [twoSidedDisagreement]
  have hforward := disagreement_reflOn_refl s
  have hbackward : (reflOn s).symm.disagreement (refl Y).symm =
      Finset.univ \ s := by
    ext y
    simp only [mem_disagreement, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro h hy
      exact h hy (Finset.mem_univ _) rfl
    · intro hy hs
      exact (hy hs).elim
  rw [hforward, hbackward, Finset.card_sdiff]
  simp
  omega

theorem twoSidedDisagreement_comm (b c : FinitePartialBijection Y Z) :
    b.twoSidedDisagreement c = c.twoSidedDisagreement b := by
  simp only [twoSidedDisagreement, disagreement_comm]

@[simp] theorem twoSidedDisagreement_symm (b c : FinitePartialBijection Y Z) :
    b.symm.twoSidedDisagreement c.symm = b.twoSidedDisagreement c := by
  simp [twoSidedDisagreement, Nat.add_comm]

theorem twoSidedDisagreement_le (b c d : FinitePartialBijection Y Z) :
    b.twoSidedDisagreement d ≤
      b.twoSidedDisagreement c + c.twoSidedDisagreement d := by
  unfold twoSidedDisagreement
  have h₁ := card_disagreement_le b c d
  have h₂ := card_disagreement_le b.symm c.symm d.symm
  omega

theorem twoSidedDisagreement_trans_le
    (a a' : FinitePartialBijection Y Z)
    (b b' : FinitePartialBijection Z W) :
    (a.trans b).twoSidedDisagreement (a'.trans b') ≤
      a.twoSidedDisagreement a' + b.twoSidedDisagreement b' := by
  unfold twoSidedDisagreement
  have h₁ := card_disagreement_trans_le a a' b b'
  rw [a.symm_trans b, a'.symm_trans b']
  have h₂ := card_disagreement_trans_le b.symm b'.symm a.symm a'.symm
  omega

/-- Failures of equivariance, counting a missing source endpoint as a
failure, for a finite family of labels. -/
noncomputable def equivarianceDefect {L : Type*} [Fintype L]
    (b : FinitePartialBijection Y Z)
    (actY : L → Equiv.Perm Y) (actZ : L → Equiv.Perm Z) : Finset (L × Y) :=
  Finset.univ.filter fun p ↦
    ∀ hx : p.2 ∈ b.source, ∀ hsx : actY p.1 p.2 ∈ b.source,
      b.apply (actY p.1 p.2) hsx ≠ actZ p.1 (b.apply p.2 hx)

end FinitePartialBijection
end GroupApproximation
