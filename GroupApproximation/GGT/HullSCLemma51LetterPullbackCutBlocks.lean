import GroupApproximation.GGT.HullSCLemma51LetterPullbackCutSides

/-!
# Quotient blocks of the certificate cut

The new quotient-null word of a cut move reads respelled inverses of the side words and of the
rest of the relator, then a tail of the old word.  This module reads their peripheral letters in
the quotient.

* `cosetLettersAt_mapHom_of_forall_rep`: a word has image values at a quotient coset if it has
  values at every representative lifting the coset.
* `cosetLettersAt_respellInv_mapHom` and its `take`/`drop` forms: the respelled inverse of a word,
  and of the prefix and suffix around one designated index, read in the quotient.
* `cosetLettersAt_respellInv_rem_mapHom`: the respelled inverse of a piece of a relator has
  bounded values in the quotient from every start.
* `CutFace.left_val_mem_of_arc`, `CutFace.right_val_mem_of_arc`: the side bounds with the arc
  read from `1`.
* `RotatedLift.arc_left`, `RotatedLift.arc_mid`: the arc read from `1` at a representative of the
  quotient coset, when the arc lies before the unknown letter, or contains it at a vertex outside
  the coset of the representative.
* `RotatedLift.tail_left`, `RotatedLift.tail_mid`: the tail of the lifted word after the arc.
-/

namespace GroupApproximation
namespace HullSC

universe u v w

variable {G : Type u} {Q : Type v} [Group G] [Group Q] {Lambda : Type w}

/-- Two elements with a common point of their cosets lie in one coset. -/
theorem inv_mul_mem_of_common_right {H : Subgroup G} {a b c : G} (h1 : a⁻¹ * c ∈ H)
    (h2 : b⁻¹ * c ∈ H) : a⁻¹ * b ∈ H := by
  have e : a⁻¹ * b = (a⁻¹ * c) * (b⁻¹ * c)⁻¹ := by group
  rw [e]
  exact H.mul_mem h1 (H.inv_mem h2)

/-- A coset condition in the source maps to the quotient. -/
theorem inv_mul_mem_map_of_mem (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (lam : Lambda) {c : Q} {cG v : G}
    (hc : c⁻¹ * q cG ∈ (D.mapSurjective q hq).fam lam) (hv : cG⁻¹ * v ∈ D.fam lam) :
    c⁻¹ * q v ∈ (D.mapSurjective q hq).fam lam := by
  have e : c⁻¹ * q v = (c⁻¹ * q cG) * q (cG⁻¹ * v) := by
    rw [map_mul, map_inv]
    group
  rw [e]
  exact mul_mem hc (Subgroup.mem_map_of_mem q hv)

/-- **A word has image values at a quotient coset** if it has values at every representative
lifting the coset. -/
theorem cosetLettersAt_mapHom_of_forall_rep (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (lam : Lambda) (B : Set G) {c : Q} {xG : G}
    {u : List (GGT.RelLetter G Lambda)}
    (h : ∀ cG : G, c⁻¹ * q cG ∈ (D.mapSurjective q hq).fam lam →
      CosetLettersAt D lam B cG xG u) :
    CosetLettersAt (D.mapSurjective q hq) lam (q '' B) c (q xG)
      (u.map (GGT.RelLetter.mapHom q)) :=
  cosetLettersAt_mapHom_of_forall D q hq lam B fun i hi hc hv =>
    h (xG * GGT.RelLetter.listVal (u.take i)) hv i hi hc
      (by rw [inv_mul_cancel]; exact one_mem _)

/-- **The respelled inverse of a word, in the quotient.** -/
theorem cosetLettersAt_respellInv_mapHom (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (lam : Lambda) (B : Set G) (c : Q) (x : G)
    {u : List (GGT.RelLetter G Lambda)} (hu : ∀ a ∈ u, D.IsLetter a)
    (h : ∀ (k : ℕ) (hk : k < u.length),
      (GGT.RelLetter.IsCompOf lam u[k] ∨ ∃ y : G, u[k] = GGT.RelLetter.base y ∧ y ∈ D.fam lam) →
        c⁻¹ * q (x * GGT.RelLetter.listVal (u.take k)) ∈ (D.mapSurjective q hq).fam lam →
          (invLetter D u[k]).val ∈ B) :
    CosetLettersAt (D.mapSurjective q hq) lam (q '' B) c (q (x * GGT.RelLetter.listVal u))
      ((respellInv D u).map (GGT.RelLetter.mapHom q)) :=
  cosetLettersAt_mapHom_of_forall_rep D q hq lam B fun cG hcG =>
    cosetLettersAt_respellInv D lam B cG x u hu fun k hk hk' hv =>
      h k hk hk' (inv_mul_mem_map_of_mem D q hq lam hcG hv)

/-- **The respelled inverse of the prefix before a designated index**, in the quotient. -/
theorem cosetLettersAt_respellInv_take_mapHom (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (lam : Lambda) (B : Set G) (c : Q) (x : G)
    {u : List (GGT.RelLetter G Lambda)} (hu : ∀ a ∈ u, D.IsLetter a) (j : ℕ)
    (h : ∀ (k : ℕ) (hk : k < u.length), k ≠ j →
      (GGT.RelLetter.IsCompOf lam u[k] ∨ ∃ y : G, u[k] = GGT.RelLetter.base y ∧ y ∈ D.fam lam) →
        c⁻¹ * q (x * GGT.RelLetter.listVal (u.take k)) ∈ (D.mapSurjective q hq).fam lam →
          (invLetter D u[k]).val ∈ B) :
    CosetLettersAt (D.mapSurjective q hq) lam (q '' B) c
      (q (x * GGT.RelLetter.listVal (u.take j)))
      ((respellInv D (u.take j)).map (GGT.RelLetter.mapHom q)) := by
  have h' : ∀ (k : ℕ) (hk : k < (u.take j).length),
      (GGT.RelLetter.IsCompOf lam (u.take j)[k] ∨
        ∃ y : G, (u.take j)[k] = GGT.RelLetter.base y ∧ y ∈ D.fam lam) →
        c⁻¹ * q (x * GGT.RelLetter.listVal ((u.take j).take k)) ∈
          (D.mapSurjective q hq).fam lam → (invLetter D (u.take j)[k]).val ∈ B := by
    intro k hk hshape hv
    have hkj : k < j := lt_of_lt_of_le hk (List.length_take_le j u)
    have hku : k < u.length := lt_of_lt_of_le hk (List.length_take_le' j u)
    rw [List.getElem_take] at hshape ⊢
    rw [List.take_take, Nat.min_eq_left hkj.le] at hv
    exact h k hku (Nat.ne_of_lt hkj) hshape hv
  exact cosetLettersAt_respellInv_mapHom D q hq lam B c x
    (fun a ha => hu a (List.mem_of_mem_take ha)) h'

/-- **The respelled inverse of the suffix after a designated index**, in the quotient, read from
the end of the word. -/
theorem cosetLettersAt_respellInv_drop_mapHom (D : GGT.RelGenSet G Lambda) (q : G →* Q)
    (hq : Function.Surjective q) (lam : Lambda) (B : Set G) (c : Q) (x : G)
    {u : List (GGT.RelLetter G Lambda)} (hu : ∀ a ∈ u, D.IsLetter a) (j : ℕ)
    (h : ∀ (k : ℕ) (hk : k < u.length), k ≠ j →
      (GGT.RelLetter.IsCompOf lam u[k] ∨ ∃ y : G, u[k] = GGT.RelLetter.base y ∧ y ∈ D.fam lam) →
        c⁻¹ * q (x * GGT.RelLetter.listVal (u.take k)) ∈ (D.mapSurjective q hq).fam lam →
          (invLetter D u[k]).val ∈ B) :
    CosetLettersAt (D.mapSurjective q hq) lam (q '' B) c (q (x * GGT.RelLetter.listVal u))
      ((respellInv D (u.drop (j + 1))).map (GGT.RelLetter.mapHom q)) := by
  have h' : ∀ (k : ℕ) (hk : k < (u.drop (j + 1)).length),
      (GGT.RelLetter.IsCompOf lam (u.drop (j + 1))[k] ∨
        ∃ y : G, (u.drop (j + 1))[k] = GGT.RelLetter.base y ∧ y ∈ D.fam lam) →
        c⁻¹ * q (x * GGT.RelLetter.listVal (u.take (j + 1)) *
          GGT.RelLetter.listVal ((u.drop (j + 1)).take k)) ∈
          (D.mapSurjective q hq).fam lam → (invLetter D (u.drop (j + 1))[k]).val ∈ B := by
    intro k hk hshape hv
    have hlen : (u.drop (j + 1)).length = u.length - (j + 1) := List.length_drop
    have hku : j + 1 + k < u.length := by omega
    rw [List.getElem_drop] at hshape ⊢
    rw [mul_assoc, ← GGT.OsinComponents.listVal_append, ← List.take_add] at hv
    exact h (j + 1 + k) hku (by omega) hshape hv
  have h1 := cosetLettersAt_respellInv_mapHom D q hq lam B c
    (x * GGT.RelLetter.listVal (u.take (j + 1))) (u := u.drop (j + 1))
    (fun a ha => hu a (List.mem_of_mem_drop ha)) h'
  rwa [mul_assoc, ← GGT.OsinComponents.listVal_append, List.take_append_drop] at h1

/-- The inverse value of a letter at the coset: an atom for a base letter in `H_λ`, a bounded
product for a peripheral letter with bounded value. -/
theorem invLetter_val_mem_boundedProducts (W : Set (List (GGT.RelLetter G Lambda)))
    (D : GGT.RelGenSet G Lambda) (lam : Lambda) {r N : ℕ} (hr1 : 1 ≤ r) (hN : 1 ≤ N)
    {a : GGT.RelLetter G Lambda} (ha : D.IsLetter a)
    (hshape : GGT.RelLetter.IsCompOf lam a ∨ ∃ y : G, a = GGT.RelLetter.base y ∧ y ∈ D.fam lam)
    (hval : GGT.RelLetter.IsCompOf lam a →
      a.val ∈ boundedProducts (pullbackAtoms W D lam r) N) :
    (invLetter D a).val ∈ boundedProducts (pullbackAtoms W D lam r) N := by
  rw [val_invLetter]
  rcases hshape with hc | ⟨y, rfl, hyH⟩
  · exact inv_mem_boundedProducts (fun _ hx => inv_mem_pullbackAtoms hx) (hval hc)
  · exact mem_boundedProducts_of_mem (inv_mem_pullbackAtoms_of_mem_base ha hyH hr1) hN

/-- **The respelled inverse of a piece of a relator**, in the quotient, from every start. -/
theorem cosetLettersAt_respellInv_rem_mapHom (W : Set (List (GGT.RelLetter G Lambda)))
    (D : GGT.RelGenSet G Lambda) (q : G →* Q) (hq : Function.Surjective q) (lam : Lambda)
    {r N : ℕ} (hr1 : 1 ≤ r) (hN : 1 ≤ N) (c : Q) (x : G)
    {rem word : List (GGT.RelLetter G Lambda)} (hrem : ∀ a ∈ rem, D.IsLetter a)
    (hword : word ∈ W) (hsub : ∀ a ∈ rem, a ∈ word) :
    CosetLettersAt (D.mapSurjective q hq) lam (q '' boundedProducts (pullbackAtoms W D lam r) N)
      c (q x) ((respellInv D rem).map (GGT.RelLetter.mapHom q)) := by
  refine cosetLettersAt_mapHom_of_forall_rep D q hq lam _ fun cG _ => ?_
  have h := cosetLettersAt_respellInv_of_subset W D lam hr1 cG
    (x * (GGT.RelLetter.listVal rem)⁻¹) hrem hword hsub
  rw [inv_mul_cancel_right] at h
  exact h.mono fun _ hx => mem_boundedProducts_of_mem hx hN

/-- Quotient blocks read one after the other, with the start of the second block given by any
lift. -/
theorem CosetLettersAt.append_mapHom {DQ : GGT.RelGenSet Q Lambda} {q : G →* Q} {lam : Lambda}
    {B : Set Q} {c : Q} {x y : G} {u v : List (GGT.RelLetter G Lambda)}
    (hu : CosetLettersAt DQ lam B c (q x) (u.map (GGT.RelLetter.mapHom q)))
    (hv : CosetLettersAt DQ lam B c (q y) (v.map (GGT.RelLetter.mapHom q)))
    (hxy : q (x * GGT.RelLetter.listVal u) = q y) :
    CosetLettersAt DQ lam B c (q x) ((u ++ v).map (GGT.RelLetter.mapHom q)) := by
  rw [List.map_append]
  refine hu.append ?_
  rwa [GGT.RelLetter.listVal_map_mapHom, ← map_mul, hxy]

/-- **A letter of `L` with no arc letter at its coset**, the arc read from `1`. -/
theorem CutFace.left_val_mem_of_arc {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {L arc R ext : List (GGT.RelLetter G Lambda)}
    (hcf : CutFace W D L arc R ext) (lam : Lambda) {r N : ℕ} (hr1 : 1 ≤ r)
    (hr : L.length + arc.length + R.length + ext.length ≤ r) (hN : r + 1 ≤ N) {i : ℕ}
    (hi : i < L.length) (hcomp : GGT.RelLetter.IsCompOf lam L[i])
    (harc : CosetLettersAt D lam (pullbackAtoms W D lam r)
      ((GGT.RelLetter.listVal L)⁻¹ * GGT.RelLetter.listVal (L.take i)) 1 arc) :
    L[i].val ∈ boundedProducts (pullbackAtoms W D lam r) N := by
  have h := harc.translate (GGT.RelLetter.listVal L)
  rw [mul_inv_cancel_left, mul_one] at h
  exact hcf.left_val_mem lam hr1 hr hN hi hcomp h

/-- **A letter of `R` with no arc letter at its coset**, the arc read from `1`. -/
theorem CutFace.right_val_mem_of_arc {W : Set (List (GGT.RelLetter G Lambda))}
    {D : GGT.RelGenSet G Lambda} {L arc R ext : List (GGT.RelLetter G Lambda)}
    (hcf : CutFace W D L arc R ext) (lam : Lambda) {r N : ℕ} (hr1 : 1 ≤ r)
    (hr : L.length + arc.length + R.length + ext.length ≤ r) (hN : r + 1 ≤ N) {i : ℕ}
    (hi : i < R.length) (hcomp : GGT.RelLetter.IsCompOf lam R[i])
    (harc : CosetLettersAt D lam (pullbackAtoms W D lam r)
      (GGT.RelLetter.listVal arc * GGT.RelLetter.listVal (R.take i)) 1 arc) :
    R[i].val ∈ boundedProducts (pullbackAtoms W D lam r) N := by
  have h := harc.translate (GGT.RelLetter.listVal L)
  rw [← mul_assoc, mul_one] at h
  exact hcf.right_val_mem lam hr1 hr hN hi hcomp h

/-- **An arc before the unknown letter**, read from `1` at a representative of the coset. -/
theorem RotatedLift.arc_left {D : GGT.RelGenSet G Lambda} {q : G →* Q}
    {hq : Function.Surjective q} {lam : Lambda} {h : G} {c : Q}
    {x y : List (GGT.RelLetter G Lambda)} (hlift : RotatedLift D q hq lam h c x y) (A : Set G)
    {arc x' : List (GGT.RelLetter G Lambda)} (hx : x = arc ++ x') {cG : G}
    (hcG : c⁻¹ * q cG ∈ (D.mapSurjective q hq).fam lam) : CosetLettersAt D lam A cG 1 arc := by
  have hav := hlift.avoid_left
  rw [hx, List.map_append, GGT.OsinComponents.avoidsFrom_append] at hav
  exact cosetLettersAt_of_avoidsFrom_mapHom D q hq lam A arc
    (by rw [map_one, mul_one]; exact hav.1) hcG

/-- **An arc through the unknown letter**, read from `1` at a representative of the coset whose
coset misses the vertex of the unknown letter. -/
theorem RotatedLift.arc_mid {D : GGT.RelGenSet G Lambda} {q : G →* Q}
    {hq : Function.Surjective q} {lam : Lambda} {h : G} {c : Q}
    {x y : List (GGT.RelLetter G Lambda)} (hlift : RotatedLift D q hq lam h c x y) (A : Set G)
    {arc y₁ tail : List (GGT.RelLetter G Lambda)}
    (harc : arc = x ++ GGT.RelLetter.comp lam h⁻¹ :: y₁) (hy : y = y₁ ++ tail) {cG : G}
    (hcG : c⁻¹ * q cG ∈ (D.mapSurjective q hq).fam lam)
    (hno : cG⁻¹ * GGT.RelLetter.listVal x ∉ D.fam lam) : CosetLettersAt D lam A cG 1 arc := by
  have hav := hlift.avoid_right
  rw [hy, List.map_append, GGT.OsinComponents.avoidsFrom_append] at hav
  rw [harc, ← List.singleton_append]
  refine CosetLettersAt.append ?_ (CosetLettersAt.append ?_ ?_)
  · exact cosetLettersAt_of_avoidsFrom_mapHom D q hq lam A x
      (by rw [map_one, mul_one]; exact hlift.avoid_left) hcG
  · exact cosetLettersAt_singleton fun _ hv => (hno (by rwa [one_mul] at hv)).elim
  · refine cosetLettersAt_of_avoidsFrom_mapHom D q hq lam A y₁ ?_ hcG
    rw [one_mul, RelWord.listVal_singleton]
    exact hav.1

/-- **The tail after an arc before the unknown letter**, in the quotient. -/
theorem RotatedLift.tail_left {D : GGT.RelGenSet G Lambda} {q : G →* Q}
    {hq : Function.Surjective q} {lam : Lambda} {h : G} {c : Q}
    {x y : List (GGT.RelLetter G Lambda)} (hlift : RotatedLift D q hq lam h c x y) (B : Set Q)
    {arc x' : List (GGT.RelLetter G Lambda)} (hx : x = arc ++ x') :
    CosetLettersAt (D.mapSurjective q hq) lam B c (q (GGT.RelLetter.listVal arc))
      (x'.map (GGT.RelLetter.mapHom q)) := by
  have hav := hlift.avoid_left
  rw [hx, List.map_append, GGT.OsinComponents.avoidsFrom_append,
    GGT.RelLetter.listVal_map_mapHom] at hav
  exact cosetLettersAt_of_avoidsFrom (D.mapSurjective q hq) lam B _ hav.2

/-- **The tail after an arc through the unknown letter**, in the quotient. -/
theorem RotatedLift.tail_mid {D : GGT.RelGenSet G Lambda} {q : G →* Q}
    {hq : Function.Surjective q} {lam : Lambda} {h : G} {c : Q}
    {x y : List (GGT.RelLetter G Lambda)} (hlift : RotatedLift D q hq lam h c x y) (B : Set Q)
    {arc y₁ tail : List (GGT.RelLetter G Lambda)}
    (harc : arc = x ++ GGT.RelLetter.comp lam h⁻¹ :: y₁) (hy : y = y₁ ++ tail) :
    CosetLettersAt (D.mapSurjective q hq) lam B c (q (GGT.RelLetter.listVal arc))
      (tail.map (GGT.RelLetter.mapHom q)) := by
  have hav := hlift.avoid_right
  rw [hy, List.map_append, GGT.OsinComponents.avoidsFrom_append,
    GGT.RelLetter.listVal_map_mapHom, mul_assoc, ← map_mul] at hav
  rw [harc, listVal_append_comp_cons]
  exact cosetLettersAt_of_avoidsFrom (D.mapSurjective q hq) lam B _ hav.2

end HullSC
end GroupApproximation

#audit_axioms GroupApproximation.HullSC.inv_mul_mem_of_common_right
#audit_axioms GroupApproximation.HullSC.inv_mul_mem_map_of_mem
#audit_axioms GroupApproximation.HullSC.cosetLettersAt_mapHom_of_forall_rep
#audit_axioms GroupApproximation.HullSC.cosetLettersAt_respellInv_mapHom
#audit_axioms GroupApproximation.HullSC.cosetLettersAt_respellInv_take_mapHom
#audit_axioms GroupApproximation.HullSC.cosetLettersAt_respellInv_drop_mapHom
#audit_axioms GroupApproximation.HullSC.invLetter_val_mem_boundedProducts
#audit_axioms GroupApproximation.HullSC.cosetLettersAt_respellInv_rem_mapHom
#audit_axioms GroupApproximation.HullSC.CosetLettersAt.append_mapHom
#audit_axioms GroupApproximation.HullSC.CutFace.left_val_mem_of_arc
#audit_axioms GroupApproximation.HullSC.CutFace.right_val_mem_of_arc
#audit_axioms GroupApproximation.HullSC.RotatedLift.arc_left
#audit_axioms GroupApproximation.HullSC.RotatedLift.arc_mid
#audit_axioms GroupApproximation.HullSC.RotatedLift.tail_left
#audit_axioms GroupApproximation.HullSC.RotatedLift.tail_mid
