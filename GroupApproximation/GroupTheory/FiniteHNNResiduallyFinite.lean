import GroupApproximation.GroupTheory.FiniteHNNFreeLabelFaithful

/-!
# Finite-base HNN extensions are residually finite

The faithful free-label action descends along every quotient of its free
label group.  A Britton-reduced nontrivial word emits a nontrivial free word;
residual finiteness of free groups chooses a finite quotient retaining it.
The descended action is then a homomorphism to a finite symmetric group that
detects the original HNN element.
-/

namespace GroupApproximation
namespace FiniteHNNFreeLabelAction

noncomputable section

universe u v

variable {G : Type u} [Group G] [Fintype G]
variable {A B : Subgroup G} (phi : A ≃* B)
variable {Q : Type v} [Group Q]

open HNNExtension

abbrev QuotientSpace (G : Type u) (Q : Type v) := G × Q

/-- The left regular base action on a descended label space. -/
def quotientBasePerm (g : G) : Equiv.Perm (QuotientSpace G Q) :=
  Equiv.prodCongr (Equiv.mulLeft g) (Equiv.refl _)

omit [Fintype G] [Group Q] in
@[simp] theorem quotientBasePerm_apply (g x : G) (w : Q) :
    quotientBasePerm (Q := Q) g (x, w) = (g * x, w) := rfl

def quotientBasePermHom : G →* Equiv.Perm (QuotientSpace G Q) where
  toFun := quotientBasePerm
  map_one' := by ext x <;> simp [quotientBasePerm]
  map_mul' g h := by ext x <;> simp [quotientBasePerm, mul_assoc]

/-- Stable permutation after mapping all free labels into `Q`. -/
def quotientStablePerm
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (q : FreeGroup (Label d) →* Q) : Equiv.Perm (QuotientSpace G Q) :=
  let V := baseIntertwiner phi d
  let label : G → Q := fun x =>
    q (FreeGroup.of ((d.compl (1 : ℤˣ)).equiv x).2)
  { toFun := fun p => (V p.1, label p.1 * p.2)
    invFun := fun p =>
      let x := V.symm p.1
      (x, (label x)⁻¹ * p.2)
    left_inv := by rintro ⟨x, w⟩; simp [V, label]
    right_inv := by rintro ⟨x, w⟩; simp [V, label] }

@[simp] theorem quotientStablePerm_apply
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (q : FreeGroup (Label d) →* Q) (x : G) (w : Q) :
    quotientStablePerm phi d q (x, w) =
      (baseIntertwiner phi d x,
        q (FreeGroup.of ((d.compl (1 : ℤˣ)).equiv x).2) * w) := rfl

theorem quotientStablePerm_covariance
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (q : FreeGroup (Label d) →* Q) (a : A) :
    quotientStablePerm phi d q * quotientBasePerm (Q := Q) (a : G) =
      quotientBasePerm (Q := Q) ((phi a : B) : G) *
        quotientStablePerm phi d q := by
  ext p <;> rcases p with ⟨x, w⟩
  · exact baseIntertwiner_mul_left phi d a x
  · simp only [Equiv.Perm.mul_apply, quotientStablePerm_apply,
      quotientBasePerm_apply, source_transversal_mul_left]

/-- The descended HNN action. -/
def quotientAction
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (q : FreeGroup (Label d) →* Q) :
    HNNExtension G A B phi →* Equiv.Perm (QuotientSpace G Q) :=
  HNNExtension.lift (quotientBasePermHom (G := G) (Q := Q))
    (quotientStablePerm phi d q) (quotientStablePerm_covariance phi d q)

@[simp] theorem quotientAction_of
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (q : FreeGroup (Label d) →* Q) (g : G) :
    quotientAction phi d q (HNNExtension.of g) = quotientBasePerm (Q := Q) g := by
  change (quotientBasePermHom (G := G) (Q := Q)) g = _
  rfl

@[simp] theorem quotientAction_t
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (q : FreeGroup (Label d) →* Q) :
    quotientAction phi d q (HNNExtension.t : HNNExtension G A B phi) =
      quotientStablePerm phi d q := by
  simp [quotientAction]

/-! ## Exact evaluation after quotienting the free labels -/

/-- A signed stable crossing emits the image of its one-letter free word. -/
theorem quotientStablePerm_zpow_apply
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (q : FreeGroup (Label d) →* Q)
    (u : ℤˣ) (x : G) (w : Q) :
    ((quotientStablePerm phi d q) ^ (u : ℤ)) (x, w) =
      (crossBase phi d u x,
        q (FreeGroup.mk [(crossLabel phi d u x, crossSign u)]) * w) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
    rfl
  · have hfree (a : Label d) :
        (FreeGroup.of a)⁻¹ = FreeGroup.mk [(a, false)] := by
      rw [FreeGroup.of, FreeGroup.inv_mk]
      rfl
    simp
    let a : Label d :=
      ((d.compl (1 : ℤˣ)).equiv ((baseIntertwiner phi d).symm x)).2
    change ((baseIntertwiner phi d).symm x, (q (FreeGroup.of a))⁻¹ * w) =
      ((baseIntertwiner phi d).symm x, q (FreeGroup.mk [(a, false)]) * w)
    rw [← map_inv, hfree]

/-- Exact evaluation of a headless Britton spelling after quotienting the
free labels. -/
theorem quotientAction_spell_apply
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (q : FreeGroup (Label d) →* Q)
    (l : List (ℤˣ × G)) (x : G) (w : Q) :
    quotientAction phi d q (HNNBritton.spell phi l) (x, w) =
      (baseRun phi d l x, q (FreeGroup.mk (labelWord phi d l x)) * w) := by
  induction l with
  | nil =>
      change (x, w) = (x, q (FreeGroup.mk []) * w)
      rw [← FreeGroup.one_eq_mk, map_one, one_mul]
  | cons p l ih =>
      rcases p with ⟨u, g⟩
      rw [HNNBritton.spell_cons]
      simp only [map_mul, Equiv.Perm.mul_apply, quotientAction_t,
        quotientAction_of, map_zpow, quotientBasePerm_apply, ih,
        quotientStablePerm_zpow_apply, baseRun_cons, labelWord_cons]
      rw [show
        (crossLabel phi d u (g * baseRun phi d l x), crossSign u) ::
            labelWord phi d l x =
          [(crossLabel phi d u (g * baseRun phi d l x), crossSign u)] ++
            labelWord phi d l x from rfl]
      rw [← FreeGroup.mul_mk, map_mul, mul_assoc]

/-- Evaluation of a full Britton word at the identity point after quotienting
the labels. -/
theorem quotientAction_wordProd_one
    (d : HNNExtension.NormalWord.TransversalPair G A B)
    (q : FreeGroup (Label d) →* Q)
    (g : G) (l : List (ℤˣ × G)) :
    quotientAction phi d q (HNNBritton.wordProd phi g l) (1, (1 : Q)) =
      (g * baseRun phi d l 1, q (FreeGroup.mk (labelWord phi d l 1))) := by
  rw [HNNBritton.wordProd, map_mul, Equiv.Perm.mul_apply, quotientAction_of,
    quotientAction_spell_apply, quotientBasePerm_apply]
  simp

/-! ## Residual finiteness -/

/-- An HNN extension of a finite group is residually finite.  The finite
quotient detecting a Britton-reduced word is the permutation action on the
finite base crossed with a finite quotient of the emitted free-label word. -/
instance finiteBaseHNN_residuallyFinite :
    Group.ResiduallyFinite (HNNExtension G A B phi) := by
  classical
  apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
  intro z hz
  obtain ⟨d⟩ := HNNExtension.NormalWord.TransversalPair.nonempty G A B
  obtain ⟨g, l, hl, hprod⟩ := HNNBritton.exists_hasSpelling phi z
  by_cases hnil : l = []
  · subst l
    have hg : g ≠ 1 := by
      intro hg
      subst g
      apply hz
      simpa using hprod.symm
    let q : FreeGroup (Label d) →* PUnit := 1
    refine ⟨Equiv.Perm (QuotientSpace G PUnit), inferInstance, inferInstance,
      quotientAction phi d q, ?_⟩
    intro hact
    have happ := DFunLike.congr_fun hact ((1 : G), (1 : PUnit))
    rw [← hprod, quotientAction_wordProd_one] at happ
    apply hg
    simpa using congrArg Prod.fst happ
  · let w₀ : FreeGroup (Label d) := FreeGroup.mk (labelWord phi d l 1)
    have hw₀ : w₀ ≠ 1 := mk_labelWord_ne_one phi d hnil hl 1
    obtain ⟨N, hN⟩ := Group.exists_finiteIndexNormalSubgroup_notMem w₀ hw₀
    letI := N.isNormal'
    letI := N.isFiniteIndex'
    let Q₀ := FreeGroup (Label d) ⧸ N.toSubgroup
    haveI : Finite Q₀ := Subgroup.finite_quotient_of_finiteIndex
    let q : FreeGroup (Label d) →* Q₀ := QuotientGroup.mk' N.toSubgroup
    have hq : q w₀ ≠ 1 := by
      intro hone
      apply hN
      exact (QuotientGroup.eq_one_iff w₀).mp hone
    refine ⟨Equiv.Perm (QuotientSpace G Q₀), inferInstance, inferInstance,
      quotientAction phi d q, ?_⟩
    intro hact
    have happ := DFunLike.congr_fun hact ((1 : G), (1 : Q₀))
    rw [← hprod, quotientAction_wordProd_one] at happ
    apply hq
    simpa [w₀] using congrArg Prod.snd happ

end


end FiniteHNNFreeLabelAction
end GroupApproximation
