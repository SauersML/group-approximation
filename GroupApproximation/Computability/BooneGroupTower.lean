import GroupApproximation.Computability.BooneGroupPresentation
import GroupApproximation.Computability.BooneGroupModularMachine
import Mathlib.GroupTheory.HNNExtension
import Mathlib.Tactic.Group

/-!
# S3: the HNN tower

Simpson's Definition 6 builds `G'_M` from the base group by adjoining one stable
letter per machine quadruple, each conjugating one copy of `G_{ab}^{MM}` onto
another copy `G_{c0}^{M²,1}`.  Mathlib's `HNNExtension` carries **one** stable
letter, so the tower has to be built one letter at a time.

The obstacle to writing that as a recursive *type* is that each stage's
subgroups live in the previous stage, so the type, its group instance and the
embedding of the base group would all have to be defined by the same recursion.
Bundling them avoids it entirely: a `Stage` carries the carrier, its group
structure, the map from the base group, and the proof that map is injective, and
`Stage.step` is an ordinary function on bundles.  The tower is then a fold, and
injectivity of the composite `ι` is maintained as an invariant rather than
proved afterwards --- `HNNExtension.of_injective` composed with the previous
stage's injectivity.

The identification attached to a quadruple is `quadEquiv`: both
`G_{ab}^{MM}` and `G_{c0}^{M²,1}` are ranges of injective embeddings of the base
group, so each is isomorphic to the base group, and the composite of one
isomorphism with the inverse of the other is the required
`G_{ab}^{MM} ≃* G_{c0}^{M²,1}`.

What is *not* here is the correctness of the tower --- that is S4, the
good-subgroup lemma, which is the only place Britton's Lemma is used.
-/

namespace GroupApproximation
namespace BooneGroup

open Base

/-- A stage of the tower: a group with an injection of the base group. -/
structure Stage where
  /-- The group at this stage. -/
  Carrier : Type
  /-- Its group structure. -/
  group : Group Carrier
  /-- The base group, embedded. -/
  ι : BaseGroup →* Carrier
  /-- The embedding is injective; maintained as an invariant up the tower. -/
  ι_injective : Function.Injective ι

attribute [instance] Stage.group

/-- The bottom of the tower: the base group itself. -/
def Stage.base : Stage where
  Carrier := BaseGroup
  group := inferInstance
  ι := MonoidHom.id _
  ι_injective := fun _ _ h => h

/-- The identification, transported into the current stage. -/
noncomputable def Stage.stepEquiv (S : Stage) {A B : Subgroup BaseGroup}
    (ψ : A ≃* B) : (A.map S.ι) ≃* (B.map S.ι) :=
  ((Subgroup.equivMapOfInjective A S.ι S.ι_injective).symm.trans ψ).trans
    (Subgroup.equivMapOfInjective B S.ι S.ι_injective)

/-- **What the transported identification does to a base element.**  It is `ψ`,
read through `ι`.  Everything the induction of Lemma 7 needs about `stepEquiv`
is this one equation. -/
theorem Stage.coe_stepEquiv (S : Stage) {A B : Subgroup BaseGroup} (ψ : A ≃* B)
    (a : BaseGroup) (ha : a ∈ A) (h : S.ι a ∈ A.map S.ι) :
    ((S.stepEquiv ψ ⟨S.ι a, h⟩ : B.map S.ι) : S.Carrier)
      = S.ι ((ψ ⟨a, ha⟩ : B) : BaseGroup) := by
  have hsymm : (Subgroup.equivMapOfInjective A S.ι S.ι_injective).symm
      ⟨S.ι a, h⟩ = ⟨a, ha⟩ := by
    apply (Subgroup.equivMapOfInjective A S.ι S.ι_injective).injective
    rw [MulEquiv.apply_symm_apply]
    refine Subtype.ext ?_
    rw [Subgroup.coe_equivMapOfInjective_apply]
  show ((Subgroup.equivMapOfInjective B S.ι S.ι_injective)
      (ψ ((Subgroup.equivMapOfInjective A S.ι S.ι_injective).symm
        ⟨S.ι a, h⟩)) : S.Carrier) = _
  rw [hsymm, Subgroup.coe_equivMapOfInjective_apply]

/-- The same, for the inverse identification. -/
theorem Stage.coe_stepEquiv_symm (S : Stage) {A B : Subgroup BaseGroup} (ψ : A ≃* B)
    (b : BaseGroup) (hb : b ∈ B) (h : S.ι b ∈ B.map S.ι) :
    (((S.stepEquiv ψ).symm ⟨S.ι b, h⟩ : A.map S.ι) : S.Carrier)
      = S.ι ((ψ.symm ⟨b, hb⟩ : A) : BaseGroup) := by
  have hsymm : (Subgroup.equivMapOfInjective B S.ι S.ι_injective).symm
      ⟨S.ι b, h⟩ = ⟨b, hb⟩ := by
    apply (Subgroup.equivMapOfInjective B S.ι S.ι_injective).injective
    rw [MulEquiv.apply_symm_apply]
    refine Subtype.ext ?_
    rw [Subgroup.coe_equivMapOfInjective_apply]
  show ((Subgroup.equivMapOfInjective A S.ι S.ι_injective)
      (ψ.symm ((Subgroup.equivMapOfInjective B S.ι S.ι_injective).symm
        ⟨S.ι b, h⟩)) : S.Carrier) = _
  rw [hsymm, Subgroup.coe_equivMapOfInjective_apply]

/-- Adjoin one stable letter, conjugating the image of `A` onto the image of `B`
along `ψ`.  This is one step of Simpson's Definition 6. -/
noncomputable def Stage.step (S : Stage) {A B : Subgroup BaseGroup} (ψ : A ≃* B) : Stage where
  Carrier := HNNExtension S.Carrier (A.map S.ι) (B.map S.ι) (S.stepEquiv ψ)
  group := inferInstance
  ι := (HNNExtension.of).comp S.ι
  ι_injective := by
    intro x y h
    apply S.ι_injective
    apply HNNExtension.of_injective
    exact h

/-- An identification of base subgroups, as the tower consumes them. -/
abbrev Identification := Σ A B : Subgroup BaseGroup, A ≃* B

/-- **The tower.**  One stable letter per identification, bottom to top. -/
noncomputable def tower : List Identification → Stage
  | [] => Stage.base
  | ⟨_, _, ψ⟩ :: l => (tower l).step ψ

/-- **The base group embeds in every stage.**  This is the invariant the bundle
carries, and it is what Britton's Lemma will be applied against. -/
theorem tower_ι_injective (l : List Identification) :
    Function.Injective (tower l).ι :=
  (tower l).ι_injective

@[simp] theorem tower_nil : tower [] = Stage.base := rfl

@[simp] theorem tower_cons (A B : Subgroup BaseGroup) (ψ : A ≃* B)
    (l : List Identification) :
    tower (⟨A, B, ψ⟩ :: l) = (tower l).step ψ := rfl

/-! ## Mapping a lower stage into the top

The induction in Simpson's Lemma 7 needs the stable letter of one level, seen in
the group at the top of the tower.  Rather than name the letters, map the whole
stage up: `liftUp l₁ l₂` is the composite of the `of`s that carry
`tower l₂` through the `l₁` levels above it, and it is injective for the same
reason each `of` is. -/

/-- The stage `l₂`, mapped into the stage `l₁ ++ l₂` above it. -/
noncomputable def liftUp : (l₁ l₂ : List Identification) →
    (tower l₂).Carrier →* (tower (l₁ ++ l₂)).Carrier
  | [], _ => MonoidHom.id _
  | _ :: l₁, l₂ => (HNNExtension.of).comp (liftUp l₁ l₂)

theorem liftUp_injective : ∀ (l₁ l₂ : List Identification),
    Function.Injective (liftUp l₁ l₂)
  | [], _ => fun _ _ h => h
  | _ :: l₁, l₂ => by
    intro x y h
    exact liftUp_injective l₁ l₂ (HNNExtension.of_injective _ h)

@[simp] theorem liftUp_nil (l₂ : List Identification) :
    liftUp [] l₂ = MonoidHom.id _ := rfl

/-- **The defining relation, seen at the top of the tower.**  A homomorphism
carries the HNN relation of one level to the same relation among the images, so
the stable letter of that level still conjugates the source subgroup onto the
target after being mapped up. -/
theorem liftUp_conj (l₁ l₂ : List Identification) {A' B' : Subgroup BaseGroup}
    (ψ : A' ≃* B') (a : (A'.map (tower l₂).ι)) :
    liftUp l₁ (⟨A', B', ψ⟩ :: l₂)
        (HNNExtension.of (((tower l₂).stepEquiv ψ a : _) : (tower l₂).Carrier))
      = liftUp l₁ (⟨A', B', ψ⟩ :: l₂) HNNExtension.t *
          liftUp l₁ (⟨A', B', ψ⟩ :: l₂)
            (HNNExtension.of ((a : _) : (tower l₂).Carrier)) *
          (liftUp l₁ (⟨A', B', ψ⟩ :: l₂) HNNExtension.t)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  exact congrArg _ (HNNExtension.equiv_eq_conj (φ := (tower l₂).stepEquiv ψ) a)

/-- **The base group's embedding is compatible with mapping up.**  Both sides
are the composite of every `of` from the bottom to the top. -/
theorem liftUp_comp_ι : ∀ (l₁ l₂ : List Identification),
    (liftUp l₁ l₂).comp (tower l₂).ι = (tower (l₁ ++ l₂)).ι
  | [], _ => MonoidHom.ext fun _ => rfl
  | _ :: l₁, l₂ => by
      show (HNNExtension.of).comp ((liftUp l₁ l₂).comp (tower l₂).ι) = _
      rw [liftUp_comp_ι l₁ l₂]
      rfl

theorem liftUp_ι_apply (l₁ l₂ : List Identification) (g : BaseGroup) :
    liftUp l₁ l₂ ((tower l₂).ι g) = (tower (l₁ ++ l₂)).ι g :=
  DFunLike.congr_fun (liftUp_comp_ι l₁ l₂) g

/-- **The defining relation on base elements.**  At the level `⟨A, B, ψ⟩` the
stable letter conjugates `ι a` to `ι (ψ a)`.  This is `equiv_eq_conj` with the
transported identification computed away. -/
theorem of_ι_conj (l : List Identification) {A B : Subgroup BaseGroup} (ψ : A ≃* B)
    (a : BaseGroup) (ha : a ∈ A) :
    (HNNExtension.of ((tower l).ι ((ψ ⟨a, ha⟩ : B) : BaseGroup)) :
        (tower (⟨A, B, ψ⟩ :: l)).Carrier)
      = HNNExtension.t * HNNExtension.of ((tower l).ι a) * HNNExtension.t⁻¹ := by
  have h := HNNExtension.equiv_eq_conj (φ := (tower l).stepEquiv ψ)
    ⟨(tower l).ι a, ⟨a, ha, rfl⟩⟩
  rw [Stage.coe_stepEquiv (tower l) ψ a ha ⟨a, ha, rfl⟩] at h
  exact h

/-! ## The identification a machine quadruple supplies

Simpson attaches to a quadruple the identification of `G_{ab}^{MM}` with
`G_{c0}^{M²,1}`.  Both are ranges of injective embeddings of the base group, so
both are isomorphic to it, and the identification is the composite. -/

/-- The isomorphism `G_{ab}^{MM} ≃* G_{c0}^{M²,1}` attached to a quadruple. -/
noncomputable def quadEquiv (a b c M : ℤ) (hM : M ≠ 0) :
    Gsub a b M M ≃* Gsub c 0 (M ^ 2) 1 :=
  (MonoidHom.ofInjective (emb_injective (a := a) (b := b) hM hM)).symm.trans
    (MonoidHom.ofInjective
      (emb_injective (a := c) (b := 0) (pow_ne_zero 2 hM) one_ne_zero))

/-- The isomorphism a *left*-moving quadruple attaches: the target is
`G_{0c}^{1,M²}` rather than `G_{c0}^{M²,1}`. -/
noncomputable def quadEquivLeft (a b c M : ℤ) (hM : M ≠ 0) :
    Gsub a b M M ≃* Gsub 0 c 1 (M ^ 2) :=
  (MonoidHom.ofInjective (emb_injective (a := a) (b := b) hM hM)).symm.trans
    (MonoidHom.ofInjective
      (emb_injective (a := 0) (b := c) one_ne_zero (pow_ne_zero 2 hM)))

/-- The identification a right-moving quadruple contributes to the tower. -/
noncomputable def quadIdentification (a b c M : ℤ) (hM : M ≠ 0) : Identification :=
  ⟨Gsub a b M M, Gsub c 0 (M ^ 2) 1, quadEquiv a b c M hM⟩

/-- The identification a *left*-moving quadruple contributes.  The direction of
the quadruple is visible in the tower: it decides which of the two target
subgroups the stable letter conjugates onto. -/
noncomputable def quadIdentificationLeft (a b c M : ℤ) (hM : M ≠ 0) : Identification :=
  ⟨Gsub a b M M, Gsub 0 c 1 (M ^ 2), quadEquivLeft a b c M hM⟩

/-! ## The tower of a machine

One stable letter for each residue pair that carries a quadruple.  Pairs with no
quadruple contribute nothing, which is the same as contributing trivial
associated subgroups. -/

/-- The residue pairs of a machine, as a list. -/
def residuePairs (mm : ModularMachine) : List (ℕ × ℕ) :=
  (List.range mm.size).flatMap fun a => (List.range mm.size).map fun b => (a, b)

theorem mem_residuePairs {mm : ModularMachine} {p : ℕ × ℕ}
    (ha : p.1 < mm.size) (hb : p.2 < mm.size) : p ∈ residuePairs mm := by
  obtain ⟨a, b⟩ := p
  simp only [residuePairs, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨a, ha, b, hb, rfl⟩

theorem lt_of_mem_residuePairs {mm : ModularMachine} {p : ℕ × ℕ}
    (h : p ∈ residuePairs mm) : p.1 < mm.size ∧ p.2 < mm.size := by
  simp only [residuePairs, List.mem_flatMap, List.mem_map, List.mem_range] at h
  obtain ⟨a, ha, b, hb, heq⟩ := h
  subst heq
  exact ⟨ha, hb⟩

/-- **The identifications a machine contributes**, one per quadruple. -/
noncomputable def machineIdentifications (mm : ModularMachine)
    (hM : (mm.size : ℤ) ≠ 0) : List Identification :=
  (residuePairs mm).filterMap fun p =>
    (mm.quad p.1 p.2).map fun q =>
      cond q.2 (quadIdentification (p.1 : ℤ) (p.2 : ℤ) (q.1 : ℤ) (mm.size : ℤ) hM)
        (quadIdentificationLeft (p.1 : ℤ) (p.2 : ℤ) (q.1 : ℤ) (mm.size : ℤ) hM)

/-- The identification of a right-moving quadruple is in the machine's list. -/
theorem quadIdentification_mem_machineIdentifications {mm : ModularMachine}
    {hM : (mm.size : ℤ) ≠ 0} {a b c : ℕ} (ha : a < mm.size) (hb : b < mm.size)
    (h : mm.quad a b = some (c, true)) :
    quadIdentification (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM
      ∈ machineIdentifications mm hM := by
  rw [machineIdentifications, List.mem_filterMap]
  refine ⟨(a, b), mem_residuePairs ha hb, ?_⟩
  rw [h]
  rfl

/-- The identification of a left-moving quadruple is in the machine's list. -/
theorem quadIdentificationLeft_mem_machineIdentifications {mm : ModularMachine}
    {hM : (mm.size : ℤ) ≠ 0} {a b c : ℕ} (ha : a < mm.size) (hb : b < mm.size)
    (h : mm.quad a b = some (c, false)) :
    quadIdentificationLeft (a : ℤ) (b : ℤ) (c : ℤ) (mm.size : ℤ) hM
      ∈ machineIdentifications mm hM := by
  rw [machineIdentifications, List.mem_filterMap]
  refine ⟨(a, b), mem_residuePairs ha hb, ?_⟩
  rw [h]
  rfl

/-- **`G'_M`**: the tower over a machine, one stable letter per quadruple. -/
noncomputable def machineTower (mm : ModularMachine) (hM : (mm.size : ℤ) ≠ 0) : Stage :=
  tower (machineIdentifications mm hM)

/-- The base group embeds in `G'_M`. -/
theorem machineTower_ι_injective (mm : ModularMachine) (hM : (mm.size : ℤ) ≠ 0) :
    Function.Injective (machineTower mm hM).ι :=
  tower_ι_injective _

/-! ## S4, the easy half

Simpson's good-subgroup lemma has two inclusions.  The one below is the routine
one and needs no Britton theory: the image of `A` lands in the subgroup
generated by `of '' A` together with the stable letter, and it lands in the range
of `of` because that is what it is.

The other inclusion --- that nothing *else* in that subgroup lands in the range
of `of` --- is the whole content of S4, is where Britton's Lemma enters, and is
not proved here. -/

variable {G : Type} [Group G] {Asub Bsub : Subgroup G} (φ : Asub ≃* Bsub)

/-- Simpson's `A'`: the subgroup generated by `A` and the stable letter. -/
def liftedSubgroup (A : Subgroup G) : Subgroup (HNNExtension G Asub Bsub φ) :=
  Subgroup.closure (HNNExtension.of '' (A : Set G) ∪ {HNNExtension.t})

theorem t_mem_liftedSubgroup (A : Subgroup G) :
    (HNNExtension.t : HNNExtension G Asub Bsub φ) ∈ liftedSubgroup φ A :=
  Subgroup.subset_closure (Or.inr rfl)

theorem of_mem_liftedSubgroup {A : Subgroup G} {a : G} (ha : a ∈ A) :
    (HNNExtension.of a : HNNExtension G Asub Bsub φ) ∈ liftedSubgroup φ A :=
  Subgroup.subset_closure (Or.inl ⟨a, ha, rfl⟩)

theorem liftedSubgroup_mono {A B : Subgroup G} (h : A ≤ B) :
    liftedSubgroup φ A ≤ liftedSubgroup φ B :=
  Subgroup.closure_mono (Set.union_subset_union_left _ (Set.image_mono h))

/-- The easy inclusion of the good-subgroup lemma. -/
theorem map_of_le_liftedSubgroup_inf (A : Subgroup G) :
    A.map (HNNExtension.of : G →* HNNExtension G Asub Bsub φ) ≤
      liftedSubgroup φ A ⊓ (HNNExtension.of : G →* HNNExtension G Asub Bsub φ).range := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨Subgroup.subset_closure ?_, ⟨a, rfl⟩⟩
  exact Or.inl ⟨a, ha, rfl⟩

/-! ### Goodness, and the pinch it licenses

Simpson's Definition 2 asks that `φ` carry `A ⊓ Asub` onto `A ⊓ Bsub`.  Its
purpose is a single algebraic step: conjugating `of a` by the stable letter,
for `a` in `A ⊓ Asub`, stays inside the image of `A`.  That step is what lets
the induction in the hard half of S4 pinch a word without leaving `A`, and it
is provable now, independently of any word machinery. -/

/-! #### The route for the half that is missing

Worked out against Mathlib's API at the pinned revision and recorded here so the
next attempt starts from a plan rather than from the statement.  The ledger's
sketch --- "turn an arbitrary word into a reduced one, pinching with `φ`" ---
can be replaced by something with no word-surgery in it at all.

Set `A₁ := Asub.comap A.subtype` and `B₁ := Bsub.comap A.subtype`, subgroups of
`A`.  Goodness makes `φ` restrict to `φ₁ : A₁ ≃* B₁`.  Let

  `ψ := HNNExtension.lift (of.comp A.subtype) t hx
        : HNNExtension A A₁ B₁ φ₁ →* HNNExtension G Asub Bsub φ`,

with `hx` supplied by `equiv_eq_conj` --- this is exactly `good_pinch` below.
Then `ψ.range = liftedSubgroup φ A`, since both are generated by `of '' A` and
`t`.

**The observation that removes the induction.**  For a letter `a` *of `A`*,

  `(a : G) ∈ Asub ↔ a ∈ A₁`

by the definition of `A₁` as a comap.  So a word over `A` is reduced in the
small extension exactly when its image is reduced in the big one: the `chain`
condition of `ReducedWord` transfers verbatim, letter by letter.  No pinching
and no induction on the number of stable letters is needed.

The proof is then: given `g ∈ liftedSubgroup φ A ⊓ of.range`, write `g = ψ u`;
take a reduced word `w` for `u` in the *small* extension (`NormalWord` exists for
every element, `prod_smul`/`prod_empty`); push `w` forward to a reduced word for
`g` in the big extension, which is legitimate by the observation; apply
`ReducedWord.toList_eq_nil_of_mem_of_range` to conclude `w.toList = []`; hence
`u = of w.head` and `g = of (w.head : G) ∈ A.map of`.

What that costs is the transfer of the `chain` field and the compatibility
`ψ (w.prod φ₁) = (pushforward w).prod φ`, both of which are structural.  It is
the only part of S4 not proved below. -/

/-- **Simpson's Definition 2.**  `φ` matches `A ⊓ Asub` with `A ⊓ Bsub`. -/
def Good (A : Subgroup G) (φ : Asub ≃* Bsub) : Prop :=
  (∀ a : Asub, (a : G) ∈ A → ((φ a : Bsub) : G) ∈ A) ∧
    (∀ b : Bsub, (b : G) ∈ A → ((φ.symm b : Asub) : G) ∈ A)

/-- **The pinch.**  For a good `A`, conjugating by the stable letter carries the
image of `A ⊓ Asub` into the image of `A`. -/
theorem good_pinch {A : Subgroup G} (hA : Good A φ) (a : Asub) (ha : (a : G) ∈ A) :
    HNNExtension.t * HNNExtension.of (a : G) * HNNExtension.t⁻¹
      ∈ A.map (HNNExtension.of : G →* HNNExtension G Asub Bsub φ) := by
  rw [← HNNExtension.equiv_eq_conj]
  exact ⟨((φ a : Bsub) : G), hA.1 a ha, rfl⟩

/-! #### The small extension

`A₁` and `B₁` are `Asub` and `Bsub` seen inside `A`, and goodness is exactly what
lets `φ` restrict to them. -/

/-- `Asub`, as a subgroup of `A`. -/
abbrev subOne (A Asub : Subgroup G) : Subgroup A := Asub.subgroupOf A

/-- The restriction of `φ` to `A₁ ≃* B₁`, which is what goodness provides. -/
def goodEquiv {A : Subgroup G} (hA : Good A φ) :
    subOne A Asub ≃* subOne A Bsub where
  toFun a := ⟨⟨(φ ⟨(a : G), a.2⟩ : G), hA.1 ⟨(a : G), a.2⟩ (a : A).2⟩,
    (φ ⟨(a : G), a.2⟩).2⟩
  invFun b := ⟨⟨(φ.symm ⟨(b : G), b.2⟩ : G), hA.2 ⟨(b : G), b.2⟩ (b : A).2⟩,
    (φ.symm ⟨(b : G), b.2⟩).2⟩
  left_inv a := by
    ext
    simp
  right_inv b := by
    ext
    simp
  map_mul' a b := by
    simp only [Subtype.ext_iff, Subgroup.coe_mul]
    exact congrArg Subtype.val
      (map_mul φ ⟨((a : A) : G), a.2⟩ ⟨((b : A) : G), b.2⟩)

/-- The natural map from the small extension to the big one. -/
def smallLift {A : Subgroup G} (hA : Good A φ) :
    HNNExtension A (subOne A Asub) (subOne A Bsub) (goodEquiv φ hA) →*
      HNNExtension G Asub Bsub φ :=
  HNNExtension.lift ((HNNExtension.of : G →* HNNExtension G Asub Bsub φ).comp A.subtype)
    HNNExtension.t (by
      intro a
      have := HNNExtension.equiv_eq_conj (φ := φ) ⟨((a : A) : G), a.2⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [show ((goodEquiv φ hA a : A) : G) = (φ ⟨((a : A) : G), a.2⟩ : G) from rfl, this]
      group)

/-- **The range of the small extension is Simpson's `A'`.**  Both are generated
by `of '' A` together with the stable letter. -/
theorem smallLift_range {A : Subgroup G} (hA : Good A φ) :
    (smallLift φ hA).range = liftedSubgroup φ A := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨u, rfl⟩
    induction u using HNNExtension.induction_on with
    | of a =>
      simp only [smallLift, HNNExtension.lift_of, MonoidHom.comp_apply,
        Subgroup.coe_subtype]
      exact Subgroup.subset_closure (Or.inl ⟨((a : A) : G), a.2, rfl⟩)
    | t =>
      simp only [smallLift, HNNExtension.lift_t]
      exact Subgroup.subset_closure (Or.inr rfl)
    | mul x y hx hy => rw [map_mul]; exact mul_mem hx hy
    | inv x hx => rw [map_inv]; exact inv_mem hx
  · refine (Subgroup.closure_le _).2 ?_
    rintro g hg
    rcases hg with ⟨a, ha, rfl⟩ | hg
    · exact ⟨HNNExtension.of ⟨a, ha⟩, by
        simp only [smallLift, HNNExtension.lift_of, MonoidHom.comp_apply,
          Subgroup.coe_subtype]⟩
    · rw [Set.mem_singleton_iff] at hg
      exact ⟨HNNExtension.t, by simp only [smallLift, HNNExtension.lift_t, hg]⟩

/-- **The observation that removes the induction.**  For a letter *of `A`*,
lying in the associated subgroup of the small extension is the same as lying in
the associated subgroup of the big one --- because the former is by definition
the comap of the latter. -/
theorem mem_toSubgroup_subOne_iff {A : Subgroup G} (u : ℤˣ) (a : A) :
    a ∈ HNNExtension.toSubgroup (subOne A Asub) (subOne A Bsub) u ↔
      (a : G) ∈ HNNExtension.toSubgroup Asub Bsub u := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp only [HNNExtension.toSubgroup_one, subOne, Subgroup.mem_subgroupOf]
  · simp only [HNNExtension.toSubgroup_neg_one, subOne, Subgroup.mem_subgroupOf]

/-- A reduced word over `A` pushes forward to a reduced word over `G`.  The
`chain` condition transfers letter by letter, by the observation above. -/
def pushWord {A : Subgroup G}
    (w : HNNExtension.NormalWord.ReducedWord A (subOne A Asub) (subOne A Bsub)) :
    HNNExtension.NormalWord.ReducedWord G Asub Bsub where
  head := (w.head : G)
  toList := w.toList.map (fun x => (x.1, (x.2 : G)))
  chain := by
    rw [List.isChain_map]
    refine w.chain.imp ?_
    rintro ⟨u, a⟩ ⟨v, b⟩ h hmem
    exact h ((mem_toSubgroup_subOne_iff u a).mpr hmem)

@[simp] theorem pushWord_toList {A : Subgroup G}
    (w : HNNExtension.NormalWord.ReducedWord A (subOne A Asub) (subOne A Bsub)) :
    (pushWord w).toList
      = w.toList.map (fun x => (x.1, (x.2 : G))) := rfl

/-- The small extension's map carries products of words to products of the
pushed-forward words. -/
theorem smallLift_prod {A : Subgroup G} (hA : Good A φ)
    (w : HNNExtension.NormalWord.ReducedWord A (subOne A Asub) (subOne A Bsub)) :
    smallLift φ hA (w.prod (goodEquiv φ hA)) = (pushWord w).prod φ := by
  rw [HNNExtension.NormalWord.ReducedWord.prod, HNNExtension.NormalWord.ReducedWord.prod, map_mul,
    map_list_prod, List.map_map, pushWord, List.map_map]
  congr 1
  refine congrArg List.prod (List.map_congr_left ?_)
  intro x _
  simp only [Function.comp_apply, map_mul, map_zpow, smallLift,
    HNNExtension.lift_t, HNNExtension.lift_of, MonoidHom.comp_apply,
    Subgroup.coe_subtype]

/-- **S4, the good-subgroup lemma.**  For a good `A`, the only elements of
Simpson's `A'` that lie in the base group are the ones that were already in `A`.

The proof needs no induction on stable letters: take a normal word for the
element in the *small* extension, push it forward --- which is legitimate
because `A₁` is the comap of `Asub`, so reducedness transfers --- and apply
Britton's Lemma in the big extension. -/
theorem liftedSubgroup_inf_range {A : Subgroup G} (hA : Good A φ) :
    liftedSubgroup φ A ⊓ (HNNExtension.of : G →* HNNExtension G Asub Bsub φ).range
      = A.map (HNNExtension.of : G →* HNNExtension G Asub Bsub φ) := by
  classical
  refine le_antisymm ?_ (map_of_le_liftedSubgroup_inf φ A)
  rintro g ⟨hg1, hg2⟩
  rw [← smallLift_range φ hA] at hg1
  obtain ⟨u, rfl⟩ := hg1
  obtain ⟨d⟩ :=
    (inferInstance :
      Nonempty (HNNExtension.NormalWord.TransversalPair A (subOne A Asub) (subOne A Bsub)))
  set w : HNNExtension.NormalWord d := u • HNNExtension.NormalWord.empty with hwdef
  have hw : w.toReducedWord.prod (goodEquiv φ hA) = u := by
    rw [hwdef]
    simp [HNNExtension.NormalWord.prod_smul, HNNExtension.NormalWord.prod_empty]
  have hmem : (pushWord w.toReducedWord).prod φ ∈
      (HNNExtension.of : G →* HNNExtension G Asub Bsub φ).range := by
    rw [← smallLift_prod φ hA, hw]
    exact hg2
  have hnil :=
    HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range φ
      (pushWord w.toReducedWord) hmem
  rw [pushWord_toList, List.map_eq_nil_iff] at hnil
  refine ⟨((w.toReducedWord.head : A) : G), (w.toReducedWord.head).2, ?_⟩
  have hu : u = HNNExtension.of w.toReducedWord.head := by
    rw [← hw, HNNExtension.NormalWord.ReducedWord.prod, hnil]
    simp
  rw [hu]
  simp only [smallLift, HNNExtension.lift_of, MonoidHom.comp_apply,
    Subgroup.coe_subtype]

/-- The pinch in the other direction. -/
theorem good_pinch_inv {A : Subgroup G} (hA : Good A φ) (b : Bsub)
    (hb : (b : G) ∈ A) :
    HNNExtension.t⁻¹ * HNNExtension.of (b : G) * HNNExtension.t
      ∈ A.map (HNNExtension.of : G →* HNNExtension G Asub Bsub φ) := by
  refine ⟨((φ.symm b : Asub) : G), hA.2 b hb, ?_⟩
  have h := HNNExtension.equiv_eq_conj (φ := φ) (φ.symm b)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  group

/-! ## S7: the last stable letter detects membership

Simpson's Theorem 8 adjoins a final stable letter `k` with both associated
subgroups equal to `A` and the identification the identity.  Then conjugation by
`k` fixes exactly the image of `A`.

The nontrivial direction is Britton for a *single* stable letter and a word of
length two: if `g ∉ A`, the word `t⁻¹ g t` is reduced --- its chain condition is
precisely `g ∈ A → -1 = 1`, which is vacuous when `g ∉ A` --- and its product
lies in the range of `of`, so Britton says it has no stable letters.  It has two.
-/

theorem conj_t_eq_iff {G' : Type} [Group G'] (A : Subgroup G') (g : G') :
    (HNNExtension.t⁻¹ * HNNExtension.of g * HNNExtension.t
      : HNNExtension G' A A (MulEquiv.refl A)) = HNNExtension.of g ↔ g ∈ A := by
  constructor
  · intro h
    by_contra hg
    let w : HNNExtension.NormalWord.ReducedWord G' A A :=
      { head := 1
        toList := [((-1 : ℤˣ), g), ((1 : ℤˣ), 1)]
        chain := by
          simp only [List.isChain_cons]
          refine ⟨?_, ?_, ?_⟩
          · rintro y - hmem
            exact absurd hmem hg
          · rintro y hy -
            simp at hy
          · simp }
    have hprod : w.prod (MulEquiv.refl A) = HNNExtension.of g := by
      have hw : w.prod (MulEquiv.refl A)
          = HNNExtension.t⁻¹ * HNNExtension.of g * HNNExtension.t := by
        show HNNExtension.of (1 : G') *
          ([((-1 : ℤˣ), g), ((1 : ℤˣ), (1 : G'))].map
            (fun x => HNNExtension.t ^ (x.1 : ℤ) * HNNExtension.of x.2)).prod = _
        have hneg : ((-1 : ℤˣ) : ℤ) = -1 := rfl
        have hone : ((1 : ℤˣ) : ℤ) = 1 := rfl
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
          map_one, one_mul, mul_one, hneg, hone, zpow_one, zpow_neg_one]
      rw [hw, h]
    have hbrit :=
      HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range (MulEquiv.refl A) w
        (by rw [hprod]; exact ⟨g, rfl⟩)
    simp only [w] at hbrit
    exact absurd hbrit (by simp)
  · intro hg
    have h := HNNExtension.equiv_eq_conj (φ := MulEquiv.refl A) ⟨g, hg⟩
    simp only [MulEquiv.refl_apply] at h
    conv_lhs => rw [h]
    group

/-- An injective hom carries intersections to intersections. -/
theorem map_inf_of_injective {G' N : Type*} [Group G'] [Group N] (f : G' →* N)
    (hf : Function.Injective f) (H K : Subgroup G') :
    (H ⊓ K).map f = H.map f ⊓ K.map f := by
  refine le_antisymm
    (le_inf (Subgroup.map_mono inf_le_left) (Subgroup.map_mono inf_le_right)) ?_
  rintro _ ⟨⟨h, hh, rfl⟩, ⟨k, hk, hk2⟩⟩
  exact ⟨h, ⟨hh, by rwa [← hf hk2]⟩, rfl⟩

/-! ## Lifting a base subgroup through the whole tower

S4 is a statement about one stable letter.  To use it up the tower, the lifted
subgroup has to be defined by the same recursion as the tower itself, and the
goodness hypothesis has to hold at every level --- which is what `GoodTower`
records.  The conclusion then follows level by level, each stage's S4 feeding
the next. -/

/-- A base subgroup, lifted through the tower: at each stable letter it becomes
Simpson's `A'`. -/
noncomputable def towerSub (A : Subgroup BaseGroup) :
    (l : List Identification) → Subgroup (tower l).Carrier
  | [] => A
  | ⟨_, _, ψ⟩ :: l => liftedSubgroup ((tower l).stepEquiv ψ) (towerSub A l)

/-- Goodness at every level of the tower. -/
def GoodTower (A : Subgroup BaseGroup) : (l : List Identification) → Prop
  | [] => True
  | ⟨_, _, ψ⟩ :: l => GoodTower A l ∧ Good (towerSub A l) ((tower l).stepEquiv ψ)

/-- **S4, iterated up the tower.**  If the lift of `A` is good at every level,
then the elements of its lift that lie in the base group are exactly those of
`A`.  This is the form Simpson's Lemma 7 and Theorem 8 use. -/
theorem towerSub_inf_range (A : Subgroup BaseGroup) :
    ∀ (l : List Identification), GoodTower A l →
      towerSub A l ⊓ (tower l).ι.range = A.map (tower l).ι
  | [], _ => by
    simp only [towerSub, tower_nil]
    show A ⊓ (MonoidHom.id BaseGroup).range = A.map (MonoidHom.id BaseGroup)
    rw [MonoidHom.range_eq_map, Subgroup.map_id, Subgroup.map_id, inf_top_eq]
  | ⟨A', B', ψ⟩ :: l, h => by
    have hprev := towerSub_inf_range A l h.1
    have hS4 := liftedSubgroup_inf_range ((tower l).stepEquiv ψ) h.2
    have hof : Function.Injective
        (HNNExtension.of :
          (tower l).Carrier →*
            HNNExtension (tower l).Carrier (A'.map (tower l).ι) (B'.map (tower l).ι)
              ((tower l).stepEquiv ψ)) :=
      HNNExtension.of_injective _
    have hle : ((tower l).ι.range).map
          (HNNExtension.of :
            (tower l).Carrier →*
              HNNExtension (tower l).Carrier (A'.map (tower l).ι) (B'.map (tower l).ι)
                ((tower l).stepEquiv ψ))
        ≤ (HNNExtension.of :
            (tower l).Carrier →*
              HNNExtension (tower l).Carrier (A'.map (tower l).ι) (B'.map (tower l).ι)
                ((tower l).stepEquiv ψ)).range := by
      rintro _ ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
    show liftedSubgroup ((tower l).stepEquiv ψ) (towerSub A l) ⊓
        ((HNNExtension.of).comp (tower l).ι).range
      = A.map ((HNNExtension.of).comp (tower l).ι)
    rw [MonoidHom.range_comp, ← Subgroup.map_map, ← hprev,
      map_inf_of_injective _ hof, ← hS4, inf_assoc, inf_eq_right.2 hle]

/-! ## `⟨t⟩'`, and the easy half of Simpson's Lemma 7

`towerTSub` is the subgroup generated by `t` at the bottom of the tower together
with every stable letter above it --- Simpson's `⟨t⟩'`.  It is defined by the
same recursion as the tower, so no stable letter has to be named individually:
`liftedSubgroup` adjoins the one at its level.

Lemma 7 asserts `T'_M = ⟨t⟩'`.  One inclusion is immediate from monotonicity
once `t` itself is in the halting subgroup, which it is, because `(0,0)` halts.
The other is the induction along a halting computation whose step is
`stable_conj_emb_right`/`_left`. -/

/-- Simpson's `⟨t⟩'`. -/
noncomputable def towerTSub : (l : List Identification) → Subgroup (tower l).Carrier
  | [] => Subgroup.closure {tGen}
  | ⟨_, _, ψ⟩ :: l => liftedSubgroup ((tower l).stepEquiv ψ) (towerTSub l)

/-- **Every level's stable letter, seen at the top, lies in `⟨t⟩'`.**  This is
what lets the induction of Lemma 7 use a different quadruple at each step
without ever naming a stable letter. -/
theorem liftUp_t_mem_towerTSub (A' B' : Subgroup BaseGroup) (ψ : A' ≃* B') :
    ∀ (l₁ l₂ : List Identification),
      liftUp l₁ (⟨A', B', ψ⟩ :: l₂) HNNExtension.t ∈
        towerTSub (l₁ ++ (⟨A', B', ψ⟩ :: l₂))
  | [], _ => t_mem_liftedSubgroup _ _
  | ⟨_, _, _⟩ :: l₁, l₂ =>
      of_mem_liftedSubgroup _ (liftUp_t_mem_towerTSub A' B' ψ l₁ l₂)

/-- **The easy half of Lemma 7.**  If `t` lies in the base subgroup, then `⟨t⟩'`
lies in its lift, at every height of the tower. -/
theorem towerTSub_le_towerSub (A : Subgroup BaseGroup) (htGen : tGen ∈ A) :
    ∀ l : List Identification, towerTSub l ≤ towerSub A l
  | [] => (Subgroup.closure_le A).2 (by
      rintro x rfl
      exact htGen)
  | ⟨_, _, ψ⟩ :: l =>
      liftedSubgroup_mono _ (towerTSub_le_towerSub A htGen l)

/-- `t` itself, at the bottom of the tower, is in `⟨t⟩'` at every height. -/
theorem ι_tGen_mem_towerTSub : ∀ l : List Identification,
    (tower l).ι tGen ∈ towerTSub l
  | [] => Subgroup.subset_closure rfl
  | ⟨_, _, _⟩ :: l => of_mem_liftedSubgroup _ (ι_tGen_mem_towerTSub l)

/-! ### Bounding a lifted subgroup from above

The hard half of Lemma 7 is an inclusion `T'_M ≤ ⟨t⟩'` at the *top* of the
tower, and `towerSub` is defined level by level, so it cannot be proved by
monotonicity: at the bottom it would ask for `T_M ≤ ⟨t⟩`, which is false.  What
is true is that `towerSub A l` is generated by the image of `A` together with
the stable letters, so any subgroup containing both contains it.  `HasLetters`
records "contains every stable letter" without naming one: at each level the
predicate descends by pulling back along `of`. -/

/-- `K` contains the stable letter of every level of `l`. -/
def HasLetters : (l : List Identification) → Subgroup (tower l).Carrier → Prop
  | [], _ => True
  | ⟨_, _, _⟩ :: l, K => HNNExtension.t ∈ K ∧ HasLetters l (K.comap HNNExtension.of)

theorem HasLetters.mono : ∀ (l : List Identification)
    {K K' : Subgroup (tower l).Carrier}, K ≤ K' → HasLetters l K → HasLetters l K'
  | [], _, _, _, _ => trivial
  | ⟨_, _, _⟩ :: l, _, _, h, hK =>
      ⟨h hK.1, HasLetters.mono l (Subgroup.comap_mono h) hK.2⟩

theorem hasLetters_towerTSub : ∀ l : List Identification, HasLetters l (towerTSub l)
  | [] => trivial
  | ⟨_, _, _⟩ :: l =>
      ⟨t_mem_liftedSubgroup _ _,
        HasLetters.mono l (fun _ hx => of_mem_liftedSubgroup _ hx)
          (hasLetters_towerTSub l)⟩

/-- **The lifted subgroup is generated by `A` and the stable letters.**  Any
subgroup of the top group containing the image of `A` and every stable letter
contains the whole lift. -/
theorem towerSub_le_of_mem (A : Subgroup BaseGroup) :
    ∀ (l : List Identification) (K : Subgroup (tower l).Carrier),
      (∀ a ∈ A, (tower l).ι a ∈ K) → HasLetters l K → towerSub A l ≤ K
  | [], _, hι, _ => fun x hx => hι x hx
  | ⟨_, _, ψ⟩ :: l, K, hι, hL => by
      show liftedSubgroup ((tower l).stepEquiv ψ) (towerSub A l) ≤ K
      refine (Subgroup.closure_le _).2 ?_
      rintro x (⟨y, hy, rfl⟩ | rfl)
      · exact towerSub_le_of_mem A l (K.comap HNNExtension.of)
          (fun a ha => hι a ha) hL.2 hy
      · exact hL.1

/-! ### Goodness lifts up the tower

Simpson checks goodness of `T_M` once, in the base group, against each
quadruple's identification.  What `towerSub_inf_range` consumes is goodness of
the *lifted* subgroup against the *transported* identification, at every level.
The two are the same statement, because S4 at the level below says the elements
of the lift that lie in the base group are exactly those of `A` --- so a
lifted-level witness is a base-group witness, where the base check applies. -/

/-- **Goodness transports up a stage.**  Goodness of `A` against `ψ` in the base
group gives goodness of the lift of `A` against the transported `ψ`, provided
the tower below is already good. -/
theorem good_lift (A : Subgroup BaseGroup) (l : List Identification)
    {A' B' : Subgroup BaseGroup} {ψ : A' ≃* B'} (hψ : Good A ψ)
    (hl : GoodTower A l) : Good (towerSub A l) ((tower l).stepEquiv ψ) := by
  have hS4 := towerSub_inf_range A l hl
  have hmap_le : A.map (tower l).ι ≤ towerSub A l := by
    rw [← hS4]; exact inf_le_left
  have hdown : ∀ g : BaseGroup, (tower l).ι g ∈ towerSub A l → g ∈ A := by
    intro g hg
    have hmem : (tower l).ι g ∈ A.map (tower l).ι := by
      rw [← hS4]; exact ⟨hg, ⟨g, rfl⟩⟩
    obtain ⟨g', hg', hgeq⟩ := hmem
    rwa [(tower l).ι_injective hgeq] at hg'
  constructor
  · rintro ⟨_, g, hg, rfl⟩ hmem
    rw [Stage.coe_stepEquiv (tower l) ψ g hg ⟨g, hg, rfl⟩]
    exact hmap_le ⟨_, hψ.1 ⟨g, hg⟩ (hdown g hmem), rfl⟩
  · rintro ⟨_, g, hg, rfl⟩ hmem
    rw [Stage.coe_stepEquiv_symm (tower l) ψ g hg ⟨g, hg, rfl⟩]
    exact hmap_le ⟨_, hψ.2 ⟨g, hg⟩ (hdown g hmem), rfl⟩

/-- **Goodness at every level, from goodness in the base group.** -/
theorem goodTower_of_forall_good (A : Subgroup BaseGroup) :
    ∀ l : List Identification, (∀ q ∈ l, Good A q.2.2) → GoodTower A l
  | [], _ => trivial
  | ⟨A', B', ψ⟩ :: l, h => by
      have hl : GoodTower A l :=
        goodTower_of_forall_good A l fun q hq => h q (List.mem_cons_of_mem _ hq)
      exact ⟨hl, good_lift A l (h ⟨A', B', ψ⟩ (List.mem_cons_self ..)) hl⟩

end BooneGroup
end GroupApproximation
