import GroupApproximation.GGT.HullSCLemma51FaceRelation
import GroupApproximation.GGT.HullSCLemma51LetterPullbackAtoms

/-!
# The rotated lift of the letter pullback

An element `y` of a quotient relative ball lifts to a source word `p` whose image avoids
`Γ_{q(H_λ)}`, with `q (listVal p) = q h` for some `h ∈ H_λ`.  The quotient-null word is
`p ++ [comp λ h⁻¹]`, and both moves of the pullback act on one of its rotations.  Every rotation
has the shape `x ++ comp λ h⁻¹ :: y`, and in the coordinates of the representative
`c = q(listVal y)⁻¹` the only peripheral letter of index `λ` read at a vertex of the base coset
`c · q(H_λ)` is the designated letter `comp λ h⁻¹` (`RotatedLift`, `exists_rotatedLift`).

The absence of other such letters is carried as avoidance of the image, which splits along
concatenations; `cosetLettersAt_of_avoidsFrom_mapHom` turns it into the vacuous coset condition
at any source coset lying over the base coset.  `CosetLettersAt.left_of_append` and
`right_of_append` restrict the coset condition to blocks.
-/

namespace GroupApproximation
namespace HullSC

universe u v w

section Blocks

variable {G : Type u} [Group G] {Lambda : Type w}

/-- The coset condition restricts to a prefix. -/
theorem CosetLettersAt.left_of_append {D : GGT.RelGenSet G Lambda} {lam : Lambda}
    {A : Set G} {c x : G} {u v : List (GGT.RelLetter G Lambda)}
    (h : CosetLettersAt D lam A c x (u ++ v)) : CosetLettersAt D lam A c x u := by
  intro i hi hc hv
  have hget := List.getElem_append_left' hi v
  have hi' : i < (u ++ v).length := by rw [List.length_append]; omega
  have htake : (u ++ v).take i = u.take i := List.take_append_of_le_length (le_of_lt hi)
  have hres := h i hi' (by rw [← hget]; exact hc) (by rw [htake]; exact hv)
  rwa [← hget] at hres

/-- The coset condition restricts to a suffix, read from the end of the prefix. -/
theorem CosetLettersAt.right_of_append {D : GGT.RelGenSet G Lambda} {lam : Lambda}
    {A : Set G} {c x : G} {u v : List (GGT.RelLetter G Lambda)}
    (h : CosetLettersAt D lam A c x (u ++ v)) :
    CosetLettersAt D lam A c (x * GGT.RelLetter.listVal u) v := by
  intro i hi hc hv
  have hget := List.getElem_append_right' u hi
  have hi' : i + u.length < (u ++ v).length := by rw [List.length_append]; omega
  have htake : (u ++ v).take (i + u.length) = u ++ v.take i := by
    rw [Nat.add_comm]
    exact List.take_length_add_append i
  have hres := h (i + u.length) hi' (by rw [← hget]; exact hc)
    (by rw [htake, GGT.OsinComponents.listVal_append, ← mul_assoc]; exact hv)
  rwa [← hget] at hres

/-- **Avoidance is the vacuous coset condition** at the base coset. -/
theorem cosetLettersAt_of_avoidsFrom (D : GGT.RelGenSet G Lambda) (lam : Lambda) (A : Set G) :
    ∀ (u : List (GGT.RelLetter G Lambda)) {c x : G},
      GGT.AvoidsFrom D.fam lam u (c⁻¹ * x) → CosetLettersAt D lam A c x u
  | [], _, _, _ => cosetLettersAt_nil D lam A _ _
  | a :: t, c, x, ⟨hhead, htail⟩ => by
      have hsingle : CosetLettersAt D lam A c x [a] :=
        cosetLettersAt_singleton fun hc hv => absurd ⟨hc, hv⟩ hhead
      have htail' : CosetLettersAt D lam A c (x * GGT.RelLetter.listVal [a]) t := by
        apply cosetLettersAt_of_avoidsFrom D lam A t
        rw [RelWord.listVal_singleton, ← mul_assoc]
        exact htail
      exact hsingle.append htail'

end Blocks

section Lift

variable {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}

/-- **Avoidance of the image gives the vacuous source coset condition** at every source coset
`cG · H_λ` lying over the base coset `c · q(H_λ)`. -/
theorem cosetLettersAt_of_avoidsFrom_mapHom (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (lam : Lambda) (A : Set G) :
    ∀ (u : List (GGT.RelLetter G Lambda)) {c : Q} {cG xG : G},
      GGT.AvoidsFrom (D.mapSurjective q hq).fam lam (u.map (GGT.RelLetter.mapHom q))
        (c⁻¹ * q xG) →
      c⁻¹ * q cG ∈ (D.mapSurjective q hq).fam lam → CosetLettersAt D lam A cG xG u
  | [], _, _, _, _, _ => cosetLettersAt_nil D lam A _ _
  | a :: t, c, cG, xG, ⟨hhead, htail⟩, hc => by
      have hsingle : CosetLettersAt D lam A cG xG [a] := by
        refine cosetLettersAt_singleton fun hcomp hv => absurd ⟨?_, ?_⟩ hhead
        · exact (GGT.RelLetter.isCompOf_mapHom q lam a).mpr hcomp
        · have e : c⁻¹ * q xG = (c⁻¹ * q cG) * q (cG⁻¹ * xG) := by
            rw [map_mul, map_inv]
            group
          rw [e]
          exact mul_mem hc (Subgroup.mem_map_of_mem q hv)
      have htail' : CosetLettersAt D lam A cG (xG * GGT.RelLetter.listVal [a]) t := by
        apply cosetLettersAt_of_avoidsFrom_mapHom D q hq lam A t _ hc
        rw [RelWord.listVal_singleton, map_mul, ← mul_assoc, ← GGT.RelLetter.val_mapHom]
        exact htail
      exact hsingle.append htail'

/-- **A rotation of the lifted quotient-null word.**  `x ++ comp λ h⁻¹ :: y` is admissible and
quotient-null, the designated letter is read at a vertex of `c · q(H_λ)`, and no other
peripheral letter of index `λ` is read at that coset (the images of `x` and `y` avoid it). -/
structure RotatedLift (D : GGT.RelGenSet G Lambda) (q : G →* Q) (hq : Function.Surjective q)
    (lam : Lambda) (h : G) (c : Q) (x y : List (GGT.RelLetter G Lambda)) : Prop where
  letters : ∀ a ∈ x ++ GGT.RelLetter.comp lam h⁻¹ :: y, D.IsLetter a
  null : q (GGT.RelLetter.listVal (x ++ GGT.RelLetter.comp lam h⁻¹ :: y)) = 1
  coset : c⁻¹ * q (GGT.RelLetter.listVal x) ∈ (D.mapSurjective q hq).fam lam
  avoid_left : GGT.AvoidsFrom (D.mapSurjective q hq).fam lam
    (x.map (GGT.RelLetter.mapHom q)) c⁻¹
  avoid_right : GGT.AvoidsFrom (D.mapSurjective q hq).fam lam
    (y.map (GGT.RelLetter.mapHom q)) (c⁻¹ * q (GGT.RelLetter.listVal x * h⁻¹))

/-- **Every rotation of the lifted word is a rotated lift.** -/
theorem exists_rotatedLift (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) {lam : Lambda} {h : G} (hh : h ∈ D.fam lam)
    {p : List (GGT.RelLetter G Lambda)} (hp : ∀ a ∈ p, D.IsLetter a)
    (havoid : GGT.AvoidsFrom (D.mapSurjective q hq).fam lam
      (p.map (GGT.RelLetter.mapHom q)) 1)
    (hqp : q (GGT.RelLetter.listVal p) = q h) (r : ℕ) :
    ∃ (x y : List (GGT.RelLetter G Lambda)) (c : Q),
      (p ++ [GGT.RelLetter.comp lam h⁻¹]).rotate r = x ++ GGT.RelLetter.comp lam h⁻¹ :: y ∧
        RotatedLift D q hq lam h c x y := by
  set e : GGT.RelLetter G Lambda := GGT.RelLetter.comp lam h⁻¹ with he
  set k := r % (p ++ [e]).length with hk
  have hklen : (p ++ [e]).length = p.length + 1 := by simp
  have hkle : k ≤ p.length := by
    have hlt : k < (p ++ [e]).length := Nat.mod_lt _ (by rw [hklen]; omega)
    omega
  have hrot : (p ++ [e]).rotate r = p.drop k ++ e :: p.take k := by
    rw [List.rotate_eq_drop_append_take_mod, ← hk, List.drop_append_of_le_length hkle,
      List.take_append_of_le_length hkle, List.append_assoc, List.singleton_append]
  have hsplit : p.map (GGT.RelLetter.mapHom q) =
      (p.take k).map (GGT.RelLetter.mapHom q) ++ (p.drop k).map (GGT.RelLetter.mapHom q) := by
    rw [← List.map_append, List.take_append_drop]
  have hav := (GGT.OsinComponents.avoidsFrom_append _ lam _ _ 1).mp (hsplit ▸ havoid)
  have hpval : q (GGT.RelLetter.listVal (p.take k)) * q (GGT.RelLetter.listVal (p.drop k)) =
      q h := by
    rw [← map_mul, ← GGT.OsinComponents.listVal_append, List.take_append_drop, hqp]
  have hhQ : q h ∈ (D.mapSurjective q hq).fam lam := Subgroup.mem_map_of_mem q hh
  refine ⟨p.drop k, p.take k, (q (GGT.RelLetter.listVal (p.take k)))⁻¹, hrot, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hp a (List.mem_of_mem_drop ha)
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact inv_mem hh
      · exact hp a (List.mem_of_mem_take ha)
  · rw [GGT.OsinComponents.listVal_append, GGT.OsinComponents.listVal_cons, map_mul, map_mul]
    have hx : q (GGT.RelLetter.listVal (p.drop k)) =
        (q (GGT.RelLetter.listVal (p.take k)))⁻¹ * q h := by
      rw [← hpval]
      group
    rw [hx, he]
    change (q (GGT.RelLetter.listVal (p.take k)))⁻¹ * q h *
      (q h⁻¹ * q (GGT.RelLetter.listVal (p.take k))) = 1
    rw [map_inv]
    group
  · rw [inv_inv, hpval]
    exact hhQ
  · rw [inv_inv]
    simpa only [GGT.RelLetter.listVal_map_mapHom, one_mul] using hav.2
  · have e1 : (q (GGT.RelLetter.listVal (p.take k)))⁻¹⁻¹ *
        q (GGT.RelLetter.listVal (p.drop k) * h⁻¹) = 1 := by
      rw [inv_inv, map_mul, ← mul_assoc, hpval, map_inv, mul_inv_cancel]
    rw [e1]
    exact hav.1

end Lift

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.CosetLettersAt.left_of_append
#audit_axioms GroupApproximation.HullSC.CosetLettersAt.right_of_append
#audit_axioms GroupApproximation.HullSC.cosetLettersAt_of_avoidsFrom
#audit_axioms GroupApproximation.HullSC.cosetLettersAt_of_avoidsFrom_mapHom
#audit_axioms GroupApproximation.HullSC.exists_rotatedLift
