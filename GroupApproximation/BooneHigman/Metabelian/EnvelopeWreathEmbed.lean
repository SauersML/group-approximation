import GroupApproximation.BooneHigman.Metabelian.EnvelopeWreathEmbedTop
import GroupApproximation.BooneHigman.Metabelian.EnvelopeSplit
import GroupApproximation.BooneHigman.Metabelian.EnvelopeWreath
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.Index
import GroupApproximation.Meta.AxiomGuard

/-!
# Zaremsky's Proposition 2.5: `S ≀ (V ⧸ S)` embeds in `S = [V, V]`

Let `V ≤ Perm (Cantor X)` contain `V_X` and be closed under localisation, with `F = V ⧸ [V, V]`
finite, and write `S = [V, V]`.  Choose `2 |F|` words of one length, `c (x, b)` for
`(x, b) ∈ F × Bool` (`exists_words`).  The map

  `wreathConeHom (p, r) = coneMap (topPerm r) (gcFun (ρ ∘ p) r)`

puts `p (r x)` inside the cone of `c (x, true)` and moves the cones by the doubled regular
action `topPerm r`.

* `wreathConeHom` is a homomorphism `W ≀ F →* Perm (Cantor X)` for any `ρ : W →* Perm` and
  commutative `F` (`coneMap_mul`, `topPerm_mul`);
* `wreathConeHom_injective`: injective when `ρ` is (`coneMap_eq_one`);
* `wreathConeHom_mem`: its image lies in any subgroup `C` closed under localisation, containing
  every `coneMap (topPerm f) 1` and the image of `ρ` (`coneMap_eq_mul`, `coneBaseHom_mem`);
* `exists_injective_wreath_commutator`: the embedding `S ≀ F ↪ S`, with `C = ⁅V, V⁆`
  (`localize_mem_commutator`, `coneMap_topPerm_mem`);
* `rnWreathEmbed : RNWreathEmbedStatement`, for `V = envelopeV X H` (`localize_mem_rn`).

Route: the product in `W ≀ F` is `(p, r)(p', r') = (x ↦ p x * p' (r⁻¹ x), r r')`, and on the
cone of `c (x, true)` both sides of the homomorphism identity act by
`ρ (p (r r' x)) * ρ (p' (r' x))`.  The finite-index hypothesis of the statement enters only as
`Finite (V ⧸ [V, V])`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.Envelope

noncomputable section

variable {X : Type*} {W : Type*} [Group W] {F : Type*} [Group F] {c : F × Bool → List X}

/-- `(p, r) ↦ coneMap (topPerm r) (gcFun (ρ ∘ p) r)`. -/
def wreathConeHom (hsep : ConesSeparated c) (ρ : W →* Equiv.Perm (Cantor X))
    (hF : ∀ a b : F, a * b = b * a) : RegularWreath W F →* Equiv.Perm (Cantor X) :=
  MonoidHom.mk' (fun q => coneMap hsep (topPerm q.right) (gcFun (fun x => ρ (q.left x)) q.right))
    fun a b => by
      show coneMap hsep (topPerm (a * b).right) (gcFun (fun x => ρ ((a * b).left x)) (a * b).right)
        = coneMap hsep (topPerm a.right) (gcFun (fun x => ρ (a.left x)) a.right) *
          coneMap hsep (topPerm b.right) (gcFun (fun x => ρ (b.left x)) b.right)
      rw [coneMap_mul]
      refine congrArg₂ (coneMap hsep) (topPerm_mul hF a.right b.right) (funext ?_)
      rintro ⟨x, _ | _⟩
      · exact (mul_one (1 : Equiv.Perm (Cantor X))).symm
      · show ρ (a.left (a.right * b.right * x) * b.left (a.right⁻¹ * (a.right * b.right * x))) =
          ρ (a.left (a.right * (b.right * x))) * ρ (b.left (b.right * x))
        rw [map_mul, mul_assoc a.right b.right x, inv_mul_cancel_left]

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.wreathConeHom

theorem wreathConeHom_injective [Nonempty X] (hsep : ConesSeparated c)
    {ρ : W →* Equiv.Perm (Cantor X)} (hF : ∀ a b : F, a * b = b * a)
    (hρ : Function.Injective ρ) : Function.Injective (wreathConeHom hsep ρ hF) := by
  refine (injective_iff_map_eq_one _).2 fun q hq => ?_
  have hq' : coneMap hsep (topPerm q.right) (gcFun (fun x => ρ (q.left x)) q.right) = 1 := hq
  have h := coneMap_eq_one hsep hq'
  have hr : q.right = 1 :=
    (mul_one q.right).symm.trans (congrArg Prod.fst (h (1, true)).1)
  refine SemidirectProduct.ext (funext fun x => hρ ?_) hr
  have e := (h (x, true)).2
  change ρ (q.left (q.right * x)) = 1 at e
  rw [hr, one_mul] at e
  exact e.trans (map_one ρ).symm

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.wreathConeHom_injective

theorem wreathConeHom_mem [Finite F] (hsep : ConesSeparated c) (ρ : W →* Equiv.Perm (Cantor X))
    (hF : ∀ a b : F, a * b = b * a) {C : Subgroup (Equiv.Perm (Cantor X))}
    (hloc : ∀ (w : List X) (g : Equiv.Perm (Cantor X)), g ∈ C → localize w g ∈ C)
    (htop : ∀ f : F, coneMap hsep (topPerm f) 1 ∈ C) (hρC : ∀ s : W, ρ s ∈ C)
    (q : RegularWreath W F) : wreathConeHom hsep ρ hF q ∈ C := by
  show coneMap hsep (topPerm q.right) (gcFun (fun x => ρ (q.left x)) q.right) ∈ C
  rw [coneMap_eq_mul hsep]
  refine C.mul_mem (htop q.right)
    (coneBaseHom_mem (G := gcFun (fun x => ρ (q.left x)) q.right) hloc hsep fun i => ?_)
  rcases i with ⟨x, _ | _⟩
  · exact C.one_mem
  · exact hρC (q.left (q.right * x))

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.wreathConeHom_mem

/-- **Zaremsky, Proposition 2.5.**  If `V ≥ V_X` is closed under localisation and
`V ⧸ [V, V]` is finite, then `[V, V] ≀ (V ⧸ [V, V])` embeds in `[V, V]`. -/
theorem exists_injective_wreath_commutator [Finite X] [Nontrivial X]
    (V : Subgroup (Equiv.Perm (Cantor X))) (hV : higmanThompsonV X ≤ V)
    (hloc : ∀ (w : List X) (g : Equiv.Perm (Cantor X)), g ∈ V → localize w g ∈ V)
    [Finite (↥V ⧸ commutator ↥V)] :
    ∃ j : RegularWreath ↥(commutator ↥V) (↥V ⧸ commutator ↥V) →* ↥(commutator ↥V),
      Function.Injective j := by
  obtain ⟨_N, c, hc, hlen⟩ := exists_words ((↥V ⧸ commutator ↥V) × Bool) X
  have hsep : ConesSeparated c := conesSeparated_of_length hc hlen
  have hF : ∀ a b : ↥V ⧸ commutator ↥V, a * b = b * a := fun a b =>
    mul_comm (a : Abelianization ↥V) b
  let ρ : ↥(commutator ↥V) →* Equiv.Perm (Cantor X) := V.subtype.comp (commutator ↥V).subtype
  have hρ : Function.Injective ρ := Subtype.val_injective.comp Subtype.val_injective
  have hρC : ∀ s : ↥(commutator ↥V), ρ s ∈ ⁅V, V⁆ := fun s => by
    have h := Subgroup.mem_map_of_mem V.subtype s.2
    rw [Subgroup.map_subtype_commutator] at h
    exact h
  have hmem : ∀ q, wreathConeHom hsep ρ hF q ∈ ⁅V, V⁆ := fun q =>
    wreathConeHom_mem hsep ρ hF (fun w _ hg => localize_mem_commutator hloc w hg)
      (fun f => coneMap_topPerm_mem hsep hlen hV f) hρC q
  let Φ := (wreathConeHom hsep ρ hF).codRestrict V fun q =>
    Subgroup.commutator_le_self V (hmem q)
  have hΦ : ∀ q, Φ q ∈ commutator ↥V := fun q => by
    have h := hmem q
    rw [← Subgroup.map_subtype_commutator] at h
    obtain ⟨s, hs, hs'⟩ := h
    have e : Φ q = s := Subtype.ext hs'.symm
    rw [e]
    exact hs
  exact ⟨Φ.codRestrict (commutator ↥V) hΦ, (MonoidHom.injective_codRestrict _ _ _).2
    ((MonoidHom.injective_codRestrict _ _ _).2 (wreathConeHom_injective hsep hF hρ))⟩

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.exists_injective_wreath_commutator

/-- **Proposition 2.5 for the envelope.**  `RNWreathEmbedStatement` holds. -/
theorem rnWreathEmbed : RNWreathEmbedStatement := by
  intro X _ _ H _ _ _hfi
  exact exists_injective_wreath_commutator (envelopeV X H) (higmanThompsonV_le_rn _)
    (fun w _ hg => localize_mem_rn _ w hg)

#audit_axioms GroupApproximation.BooneHigman.Metabelian.Envelope.rnWreathEmbed

end

end GroupApproximation.BooneHigman.Metabelian.Envelope
