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

/-- Adjoin one stable letter, conjugating the image of `A` onto the image of `B`
along `ψ`.  This is one step of Simpson's Definition 6. -/
noncomputable def Stage.step (S : Stage) {A B : Subgroup BaseGroup} (ψ : A ≃* B) : Stage where
  Carrier :=
    HNNExtension S.Carrier (A.map S.ι) (B.map S.ι)
      (((Subgroup.equivMapOfInjective A S.ι S.ι_injective).symm.trans ψ).trans
        (Subgroup.equivMapOfInjective B S.ι S.ι_injective))
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

/-- The identification a quadruple contributes to the tower. -/
noncomputable def quadIdentification (a b c M : ℤ) (hM : M ≠ 0) : Identification :=
  ⟨Gsub a b M M, Gsub c 0 (M ^ 2) 1, quadEquiv a b c M hM⟩

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

/-- **The identifications a machine contributes**, one per quadruple. -/
noncomputable def machineIdentifications (mm : ModularMachine)
    (hM : (mm.size : ℤ) ≠ 0) : List Identification :=
  (residuePairs mm).filterMap fun p =>
    (mm.quad p.1 p.2).map fun q =>
      quadIdentification (p.1 : ℤ) (p.2 : ℤ) (q.1 : ℤ) (mm.size : ℤ) hM

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

end BooneGroup
end GroupApproximation
