import GroupApproximation.GGT.HullSCLemma51EmbeddedProducer
import GroupApproximation.GGT.HullSCLemma44QuotientRelGenSet
import GroupApproximation.GGT.OsinTheorem54SeparatingCosets
import GroupApproximation.Meta.AxiomGuard

/-!
# Atoms and lifts for the letter pullback

The letter pullback (`QuotientPeripheralLetterPullbackAt`) writes every element of a quotient
relative ball as the image of a bounded product of *atoms*.  An atom at radius `r` is a
peripheral letter value of a relator, or an element of the source relative ball of radius `r`
or its inverse (`pullbackAtoms`).  This module holds what the induction needs about atoms, lifts
and bounded products, independently of any move.

* `inv_mem_pullbackAtoms`, `pullbackAtoms_mono`: atoms are closed under inversion and grow with
  the radius.
* `inv_mem_pullbackAtoms_of_mem_base`: the inverse of a base letter lying in `H_λ` is an atom.
* `image_boundedProducts_subset`, `boundedProducts_boundedProducts_subset`: products of images
  are images of products, and products of bounded products are bounded products.
* `exists_lift_of_mem_relBall_mapSurjective`: an element of a quotient relative ball is the
  image of a source word whose image avoids `Γ_{q(H_λ)}`, and it has a lift in `H_λ`.
* `avoidsFrom_of_avoidsFrom_mapHom`, `mem_relBall_of_avoids_mapHom`: a source word whose image
  avoids in the quotient avoids in the source, so a null lift puts the lift in a source ball.
-/

namespace GroupApproximation
namespace HullSC

open scoped Pointwise

universe u v w

section Atoms

variable {G : Type u} [Group G] {Lambda : Type w}

/-- **The atoms of the letter pullback at radius `r`.** -/
def pullbackAtoms (W : Set (List (GGT.RelLetter G Lambda))) (D : GGT.RelGenSet G Lambda)
    (lam : Lambda) (r : ℕ) : Set G :=
  peripheralLetterValues W ∪ D.relBall lam r ∪ (D.relBall lam r)⁻¹

theorem inv_mem_pullbackAtoms {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {lam : Lambda} {r : ℕ} {x : G}
    (hx : x ∈ pullbackAtoms W D lam r) : x⁻¹ ∈ pullbackAtoms W D lam r := by
  rcases hx with (hx | hx) | hx
  · exact Or.inl (Or.inl (inv_mem_peripheralLetterValues W x hx))
  · exact Or.inr (Set.mem_inv.mpr (by rw [inv_inv]; exact hx))
  · exact Or.inl (Or.inr (Set.mem_inv.mp hx))

theorem pullbackAtoms_mono {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {lam : Lambda} {r r' : ℕ} (h : r ≤ r') :
    pullbackAtoms W D lam r ⊆ pullbackAtoms W D lam r' := by
  rintro x ((hx | hx) | hx)
  · exact Or.inl (Or.inl hx)
  · exact Or.inl (Or.inr (GGT.OsinComponents.relBall_mono_radius D lam h hx))
  · exact Or.inr (Set.mem_inv.mpr
      (GGT.OsinComponents.relBall_mono_radius D lam h (Set.mem_inv.mp hx)))

theorem relBall_subset_pullbackAtoms (W : Set (List (GGT.RelLetter G Lambda)))
    (D : GGT.RelGenSet G Lambda) (lam : Lambda) (r : ℕ) :
    D.relBall lam r ⊆ pullbackAtoms W D lam r :=
  fun _ hx => Or.inl (Or.inr hx)

theorem peripheralLetterValues_subset_pullbackAtoms (W : Set (List (GGT.RelLetter G Lambda)))
    (D : GGT.RelGenSet G Lambda) (lam : Lambda) (r : ℕ) :
    peripheralLetterValues W ⊆ pullbackAtoms W D lam r :=
  fun _ hx => Or.inl (Or.inl hx)

/-- **The inverse of a base letter lying in `H_λ` is an atom**, at every positive radius: the
one-letter word is a path avoiding `Γ_{H_λ}`. -/
theorem inv_mem_pullbackAtoms_of_mem_base {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {lam : Lambda} {r : ℕ} {y : G} (hy : y ∈ D.base)
    (hH : y ∈ D.fam lam) (hr : 1 ≤ r) : y⁻¹ ∈ pullbackAtoms W D lam r :=
  Or.inr (Set.mem_inv.mpr (by
    rw [inv_inv]
    exact GGT.OsinComponents.relBall_mono_radius D lam hr
      (GGT.OsinComponents.mem_relBall_of_mem_base D lam hH hy)))

/-- A list of images has a list of preimages with the same length and product image. -/
theorem exists_preimage_list {Q : Type v} [Group Q] (q : G →* Q) (B : Set G) :
    ∀ l : List Q, (∀ x ∈ l, x ∈ q '' B) →
      ∃ l' : List G, l'.length = l.length ∧ (∀ x ∈ l', x ∈ B) ∧ q l'.prod = l.prod
  | [], _ => ⟨[], rfl, by simp, by simp⟩
  | x :: t, h => by
      obtain ⟨y, hy, rfl⟩ := h x List.mem_cons_self
      obtain ⟨t', hlen, hmem, hprod⟩ :=
        exists_preimage_list q B t (fun z hz => h z (List.mem_cons_of_mem _ hz))
      refine ⟨y :: t', by rw [List.length_cons, List.length_cons, hlen], ?_, ?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hy
        · exact hmem z hz
      · rw [List.prod_cons, map_mul, hprod, List.prod_cons]

/-- **A bounded product of images is the image of a bounded product.** -/
theorem image_boundedProducts_subset {Q : Type v} [Group Q] (q : G →* Q) (B : Set G)
    (M : ℕ) : boundedProducts (q '' B) M ⊆ q '' boundedProducts B M := by
  rintro z ⟨l, hl, hmem, rfl⟩
  obtain ⟨l', hlen, hmem', hprod⟩ := exists_preimage_list q B l hmem
  exact ⟨l'.prod, ⟨l', by rw [hlen]; exact hl, hmem', rfl⟩, hprod⟩

/-- **A bounded product of bounded products is a bounded product.** -/
theorem boundedProducts_boundedProducts_subset (B : Set G) (N M : ℕ) :
    boundedProducts (boundedProducts B N) M ⊆ boundedProducts B (M * N) := by
  rintro z ⟨l, hl, hmem, rfl⟩
  induction l generalizing M with
  | nil => exact ⟨[], Nat.zero_le _, by simp, rfl⟩
  | cons x t ih =>
      obtain ⟨lx, hlx, hmx, rfl⟩ := hmem x List.mem_cons_self
      obtain ⟨lt, hlt, hmt, hprod⟩ :=
        ih t.length le_rfl (fun y hy => hmem y (List.mem_cons_of_mem _ hy))
      have hl' : t.length + 1 ≤ M := by simpa using hl
      refine ⟨lx ++ lt, ?_, ?_, ?_⟩
      · rw [List.length_append]
        have e : (t.length + 1) * N = t.length * N + N := Nat.add_one_mul _ _
        have h1 : lx.length + lt.length ≤ (t.length + 1) * N := by omega
        exact le_trans h1 (Nat.mul_le_mul_right N hl')
      · intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hmx y hy
        · exact hmt y hy
      · rw [List.prod_append, hprod, List.prod_cons]

end Atoms

section Lift

variable {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}

/-- **An element of a quotient relative ball lifts.**  It is the image of a source word of no
greater length whose image avoids `Γ_{q(H_λ)}`, and it is the image of an element of `H_λ`. -/
theorem exists_lift_of_mem_relBall_mapSurjective (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) {lam : Lambda} {n : ℕ} {y : Q}
    (hy : y ∈ (D.mapSurjective q hq).relBall lam n) :
    ∃ p : List (GGT.RelLetter G Lambda), (∀ a ∈ p, D.IsLetter a) ∧ p.length ≤ n ∧
      q (GGT.RelLetter.listVal p) = y ∧
      GGT.AvoidsFrom (D.mapSurjective q hq).fam lam (p.map (GGT.RelLetter.mapHom q)) 1 ∧
      ∃ h ∈ D.fam lam, q h = y := by
  obtain ⟨hyfam, word, hword, hval, havoid, hlen⟩ := hy
  obtain ⟨p, hp, hmap, hplen⟩ :=
    GGT.RelGenSet.exists_sourceWord_of_admissible_mapSurjective D q hq word hword
  obtain ⟨h, hh, hqh⟩ := Subgroup.mem_map.mp hyfam
  refine ⟨p, hp, by omega, ?_, by rw [hmap]; exact havoid, h, hh, hqh⟩
  rw [GGT.RelGenSet.map_listVal_sourceWord q hmap, hval]

/-- **Avoidance in the quotient pulls back to the source.**  A vertex of `H_λ` maps to a vertex
of `q(H_λ)`, and the tag of a letter is kept by `mapHom`. -/
theorem avoidsFrom_of_avoidsFrom_mapHom (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (lam : Lambda) :
    ∀ (p : List (GGT.RelLetter G Lambda)) (v : G),
      GGT.AvoidsFrom (D.mapSurjective q hq).fam lam (p.map (GGT.RelLetter.mapHom q)) (q v) →
        GGT.AvoidsFrom D.fam lam p v
  | [], _, _ => trivial
  | a :: t, v, ⟨hhead, htail⟩ => by
      refine ⟨fun hcon => hhead ⟨(GGT.RelLetter.isCompOf_mapHom q lam a).mpr hcon.1,
        Subgroup.mem_map_of_mem q hcon.2⟩, ?_⟩
      apply avoidsFrom_of_avoidsFrom_mapHom D q hq lam t (v * a.val)
      simpa only [GGT.RelLetter.val_mapHom, map_mul] using htail

/-- **A lift whose image avoids lies in the source relative ball of its length.** -/
theorem mem_relBall_of_avoids_mapHom (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) {lam : Lambda} {p : List (GGT.RelLetter G Lambda)}
    (hp : ∀ a ∈ p, D.IsLetter a)
    (havoid : GGT.AvoidsFrom (D.mapSurjective q hq).fam lam
      (p.map (GGT.RelLetter.mapHom q)) 1)
    {h : G} (hh : h ∈ D.fam lam) (hval : GGT.RelLetter.listVal p = h) :
    h ∈ D.relBall lam p.length :=
  ⟨hh, p, hp, hval,
    avoidsFrom_of_avoidsFrom_mapHom D q hq lam p 1 (by rw [map_one]; exact havoid), le_rfl⟩

end Lift

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.inv_mem_pullbackAtoms
#audit_axioms GroupApproximation.HullSC.pullbackAtoms_mono
#audit_axioms GroupApproximation.HullSC.inv_mem_pullbackAtoms_of_mem_base
#audit_axioms GroupApproximation.HullSC.image_boundedProducts_subset
#audit_axioms GroupApproximation.HullSC.boundedProducts_boundedProducts_subset
#audit_axioms GroupApproximation.HullSC.exists_lift_of_mem_relBall_mapSurjective
#audit_axioms GroupApproximation.HullSC.avoidsFrom_of_avoidsFrom_mapHom
#audit_axioms GroupApproximation.HullSC.mem_relBall_of_avoids_mapHom
