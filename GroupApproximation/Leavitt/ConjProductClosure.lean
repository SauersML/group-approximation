import GroupApproximation.Leavitt.HilbertHotelCover

/-!
# Conjugate-product words and the normal-closure induction

`HilbertHotelCover.conjProduct` is a *formal* product of conjugates of a fixed
defect word: a list of (conjugator, sign) pairs `l` spells

`∏ (p : l), p.1 * d^{±1} * p.1⁻¹`.

Two facts about that shape are needed there, and both are pure group theory
with nothing Leavitt-specific in them:

* **saturation in word form** -- if `d` normally generates the target of a
  surjection `f`, then *every* target element is `f` of such a product;
* **membership** -- any homomorphic image of such a product lies in the normal
  closure of the corresponding image of `d`.

This file proves both over an arbitrary group, in the namespace `ConjWord`, and
then instantiates them at the cover presentation.  The generic layer is stated
for a bare group rather than for `FreeGroup ι`, so the two-block sum alphabet
of `HilbertHotelCoverBlock` re-instantiates it without any porting.

## The shape of the argument

`Subgroup.normalClosure s` is by definition `Subgroup.closure (conjugatesOfSet s)`,
so `Subgroup.closure_induction` applies directly and the four clauses match the
four list operations one-to-one:

| closure clause | list operation |
| -------------- | -------------- |
| `1` | `[]` |
| a conjugate `x * f d * x⁻¹` | a one-element list, at a chosen preimage of `x` |
| `a * b` | `++` |
| `a⁻¹` | `invList` -- reverse, and flip every sign |

Surjectivity of `f` is used in exactly one place: the generator clause, to name
a preimage of the conjugator.  That is why the statement cannot be weakened to
"`f` has dense image" or similar -- the *word* has to live upstairs.

The converse direction (`conjWord_mem_of_mem`) is the reason the two are not
the same statement: normal closures only push *forward* along a surjection, so
membership downstairs is not membership upstairs, and the cover file has to
impose its saturation relators rather than inherit them.

## Open leaves

None.  Every result here is unconditional; in particular
`HilbertHotel.Cover.coverInputs_nonempty` discharges the `CoverInputs` record
of `HilbertHotelCover`, which that file carried as its single mathematical
residual.
-/

namespace GroupApproximation
namespace ConjWord

/-! ## 1.  The word calculus -/

section Word

variable {G : Type*} [Group G]

/-- The conjugate-product word attached to a defect `d` and a list of
conjugators-with-sign.  The body is literally the one used by
`HilbertHotel.Cover.conjProduct`, so the two agree by `rfl`. -/
def conjWord (d : G) (l : List (G × Bool)) : G :=
  (l.map fun p => p.1 * (if p.2 then d else d⁻¹) * p.1⁻¹).prod

@[simp] theorem conjWord_nil (d : G) : conjWord d [] = 1 := by
  simp [conjWord]

theorem conjWord_cons (d c : G) (b : Bool) (l : List (G × Bool)) :
    conjWord d ((c, b) :: l) = c * (if b then d else d⁻¹) * c⁻¹ * conjWord d l := by
  simp [conjWord]

theorem conjWord_singleton (d c : G) (b : Bool) :
    conjWord d [(c, b)] = c * (if b then d else d⁻¹) * c⁻¹ := by
  simp [conjWord]

theorem conjWord_append (d : G) (l₁ l₂ : List (G × Bool)) :
    conjWord d (l₁ ++ l₂) = conjWord d l₁ * conjWord d l₂ := by
  simp [conjWord]

/-- The list spelling the inverse word: reverse the order and flip every
sign. -/
def invList (l : List (G × Bool)) : List (G × Bool) :=
  (l.map fun p => (p.1, !p.2)).reverse

omit [Group G] in
@[simp] theorem invList_nil : invList ([] : List (G × Bool)) = [] := rfl

omit [Group G] in
theorem invList_cons (c : G) (b : Bool) (l : List (G × Bool)) :
    invList ((c, b) :: l) = invList l ++ [(c, !b)] := by
  simp [invList]

theorem conjWord_invList (d : G) (l : List (G × Bool)) :
    conjWord d (invList l) = (conjWord d l)⁻¹ := by
  induction l with
  | nil => simp
  | cons p l ih =>
      obtain ⟨c, b⟩ := p
      rw [invList_cons, conjWord_append, ih, conjWord_singleton, conjWord_cons]
      cases b <;> simp [mul_assoc]

/-- A conjugate-product word lands in any normal subgroup containing the
defect.  Each factor is a conjugate of `d` or of `d⁻¹`; normality handles the
conjugation, `inv_mem` the sign, and `mul_mem` the list. -/
theorem conjWord_mem_of_mem {H : Subgroup G} (hH : H.Normal) {d : G} (hd : d ∈ H)
    (l : List (G × Bool)) : conjWord d l ∈ H := by
  induction l with
  | nil =>
      rw [conjWord_nil]
      exact one_mem H
  | cons p l ih =>
      obtain ⟨c, b⟩ := p
      rw [conjWord_cons]
      refine mul_mem (hH.conj_mem _ ?_ c) ih
      cases b with
      | false => simpa using inv_mem hd
      | true => simpa using hd

/-- The special case that names the smallest such subgroup. -/
theorem conjWord_mem_normalClosure (d : G) (l : List (G × Bool)) :
    conjWord d l ∈ Subgroup.normalClosure ({d} : Set G) :=
  conjWord_mem_of_mem (Subgroup.normalClosure_normal (s := ({d} : Set G)))
    (Subgroup.subset_normalClosure (Set.mem_singleton_iff.mpr rfl)) l

end Word

/-! ## 2.  Transport along a homomorphism -/

section Hom

variable {F H : Type*} [Group F] [Group H]

/-- A homomorphism carries a conjugate-product word to the conjugate-product
word of the image defect, over the image conjugators.  This is the list-level
form of `map_list_prod`. -/
theorem map_conjWord (φ : F →* H) (d : F) (l : List (F × Bool)) :
    φ (conjWord d l) = conjWord (φ d) (l.map fun p => (φ p.1, p.2)) := by
  induction l with
  | nil => simp
  | cons p l ih =>
      obtain ⟨c, b⟩ := p
      -- `simp only` rather than `rw`: the map has to beta-reduce before
      -- `conjWord_cons` can see a pair literal at the head of the list.
      simp only [List.map_cons]
      rw [conjWord_cons, conjWord_cons, map_mul, map_mul, map_mul, map_inv, ih]
      cases b <;> simp

/-- **Generic membership.**  Every homomorphic image of a conjugate-product
word of `d` lies in the normal closure of the image of `d`. -/
theorem map_conjWord_mem_normalClosure (φ : F →* H) (d : F) (l : List (F × Bool)) :
    φ (conjWord d l) ∈ Subgroup.normalClosure ({φ d} : Set H) := by
  rw [map_conjWord]
  exact conjWord_mem_normalClosure (φ d) _

end Hom

/-! ## 3.  The closure induction -/

section Closure

variable {F G : Type*} [Group F] [Group G]

/-- **The closure induction.**  If `d` maps to a normal generator of `G` under
a surjection `f`, then every element of `G` is the image of a conjugate-product
word in `d`.

The four clauses of `Subgroup.closure_induction` over
`Subgroup.normalClosure {f d} = Subgroup.closure (conjugatesOfSet {f d})` are
answered by `[]`, a singleton list at a chosen preimage of the conjugator,
`++`, and `invList`. -/
theorem exists_conjWord (f : F →* G) (hf : Function.Surjective f) (d : F)
    (hd : Subgroup.normalClosure ({f d} : Set G) = ⊤) (g : G) :
    ∃ l : List (F × Bool), f (conjWord d l) = g := by
  have hg : g ∈ Subgroup.normalClosure ({f d} : Set G) := by
    rw [hd]
    exact Subgroup.mem_top g
  refine Subgroup.closure_induction (fun x hx => ?_) ?_
    (fun x y _ _ ihx ihy => ?_) (fun x _ ihx => ?_) hg
  · obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hx
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    obtain ⟨c₀, rfl⟩ := hf c
    refine ⟨[(c₀, true)], ?_⟩
    rw [conjWord_singleton]
    simpa using hc
  · exact ⟨[], by simp⟩
  · obtain ⟨l₁, h₁⟩ := ihx
    obtain ⟨l₂, h₂⟩ := ihy
    exact ⟨l₁ ++ l₂, by rw [conjWord_append, map_mul, h₁, h₂]⟩
  · obtain ⟨l, hl⟩ := ihx
    exact ⟨invList l, by rw [conjWord_invList, map_inv, hl]⟩

end Closure

end ConjWord

/-! ## 4.  The Hilbert-hotel cover instances -/

namespace HilbertHotel
namespace Cover

/-- The cover file's formal conjugate product is the generic word at the defect
word: the two definitions have the same body. -/
theorem conjProduct_eq_conjWord (l : List (FreeGroup (Fin generatorCount) × Bool)) :
    conjProduct l = ConjWord.conjWord defectWord l := rfl

/-- The defect word represents the defect of the model, by the defining
property of `liftWord`. -/
theorem freeToModel_defectWord : freeToModel defectWord = defectModel :=
  freeToModel_liftWord defectModel

/-- Model saturation, restated at the image of the defect *word*, which is the
form the closure induction consumes. -/
theorem normalClosure_freeToModel_defectWord_eq_top :
    Subgroup.normalClosure ({freeToModel defectWord} : Set Model) = ⊤ := by
  rw [freeToModel_defectWord]
  exact normalClosure_defectModel_eq_top

/-- **The open input of `HilbertHotelCover`, discharged.**  Every model element
is the image of a formal product of conjugates of the defect word.  This is
`normalClosure_defectModel_eq_top` unfolded through `freeToModel_surjective`. -/
theorem model_exists_conjProduct (g : Model) :
    ∃ l : List (FreeGroup (Fin generatorCount) × Bool),
      freeToModel (conjProduct l) = g := by
  obtain ⟨l, hl⟩ :=
    ConjWord.exists_conjWord freeToModel freeToModel_surjective defectWord
      normalClosure_freeToModel_defectWord_eq_top g
  refine ⟨l, ?_⟩
  rw [conjProduct_eq_conjWord]
  exact hl

/-- The cover inputs are inhabited: the record is no longer an assumption. -/
theorem coverInputs_nonempty : Nonempty CoverInputs :=
  ⟨⟨model_exists_conjProduct⟩⟩

/-- **The `conjProduct_mem` clause of `CoverResiduals`, discharged.**  The
defect of the cover group is `wordInCoverGroup C defectWord` by definition, so
this is the generic membership lemma at `φ := wordInCoverGroup C`. -/
theorem conjProduct_mem_normalClosure (C : CoverInputs)
    (l : List (FreeGroup (Fin generatorCount) × Bool)) :
    wordInCoverGroup C (conjProduct l) ∈
      Subgroup.normalClosure ({defect C} : Set (CoverGroup C)) := by
  have hdefect : wordInCoverGroup C defectWord = defect C := rfl
  have h :=
    ConjWord.map_conjWord_mem_normalClosure (wordInCoverGroup C) defectWord l
  rw [hdefect] at h
  rw [conjProduct_eq_conjWord]
  exact h

end Cover
end HilbertHotel
end GroupApproximation
