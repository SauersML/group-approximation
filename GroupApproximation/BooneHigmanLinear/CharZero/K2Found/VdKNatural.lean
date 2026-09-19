import GroupApproximation.BooneHigmanLinear.CharZero.K2Found.VdKUnique
import GroupApproximation.Steinberg.Functoriality

/-!
# Naturality of van der Kallen's elements `X(v, w)` (k2-poly, piece F.1)

For a ring map `f : A →+* B`, the coefficient map `ringMap f : St(n, A) → St(n, B)` sends
`X(v, w)` to `X(f ∘ v, f ∘ w)`. On the way, `ringMap f` commutes with the row and column products
of vdK 3.7 (`ringMap_rowProd`, `ringMap_colProd`), with `x(i, j)` of vdK 3.10 (`ringMap_xvw`,
`ringMap_xz`) and with `x_i(j; k)` of vdK 3.20 (`ringMap_xk`). The main statement is
`elements_natural`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySimpa false

namespace GroupApproximation
namespace BooneHigmanLinear
namespace K2Found
namespace VdK

open scoped commutatorElement Matrix
open GroupApproximation.SteinbergGroup

variable {I A B : Type*} [Fintype I] [DecidableEq I] [CommRing A] [CommRing B]

theorem comp_single (f : A →+* B) (s : I) (b : A) :
    (f ∘ Pi.single s b : I → B) = Pi.single s (f b) := by
  funext t
  by_cases h : t = s
  · rw [h, Function.comp_apply, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Function.comp_apply, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

theorem comp_add (f : A →+* B) (u v : I → A) : (f ∘ (u + v) : I → B) = f ∘ u + f ∘ v :=
  funext fun t => map_add f (u t) (v t)

theorem comp_smul (f : A →+* B) (c : A) (u : I → A) : (f ∘ (c • u) : I → B) = f c • (f ∘ u) :=
  funext fun t => map_mul f c (u t)

theorem ringMap_rowProd (f : A →+* B) (r : I) (j : I → A) :
    ringMap f (rowProd r j) = rowProd r (f ∘ j) := by
  refine eq_of_add_of_single (f := fun j : I → A => ringMap f (rowProd r j))
    (g := fun j : I → A => rowProd r (f ∘ j)) (fun u v => ?_) (fun u v => ?_) (fun s b => ?_) j
  · show ringMap f (rowProd r (u + v)) = ringMap f (rowProd r u) * ringMap f (rowProd r v)
    rw [rowProd_add, map_mul]
  · show rowProd r (f ∘ (u + v)) = rowProd r (f ∘ u) * rowProd r (f ∘ v)
    rw [comp_add, rowProd_add]
  · show ringMap f (rowProd r (Pi.single s b)) = rowProd r (f ∘ Pi.single s b)
    rw [comp_single]
    by_cases hrs : r = s
    · rw [hrs, rowProd_single_self, rowProd_single_self, map_one]
    · rw [rowProd_single_ne r s hrs, rowProd_single_ne r s hrs, ringMap_x]

theorem ringMap_colProd (f : A →+* B) (r : I) (i : I → A) :
    ringMap f (colProd r i) = colProd r (f ∘ i) := by
  refine eq_of_add_of_single (f := fun i : I → A => ringMap f (colProd r i))
    (g := fun i : I → A => colProd r (f ∘ i)) (fun u v => ?_) (fun u v => ?_) (fun s b => ?_) i
  · show ringMap f (colProd r (u + v)) = ringMap f (colProd r u) * ringMap f (colProd r v)
    rw [colProd_add, map_mul]
  · show colProd r (f ∘ (u + v)) = colProd r (f ∘ u) * colProd r (f ∘ v)
    rw [comp_add, colProd_add]
  · show ringMap f (colProd r (Pi.single s b)) = colProd r (f ∘ Pi.single s b)
    rw [comp_single]
    by_cases hsr : s = r
    · rw [hsr, colProd_single_self, colProd_single_self, map_one]
    · rw [colProd_single_ne r s hsr, colProd_single_ne r s hsr, ringMap_x]

theorem ringMap_xvw (f : A →+* B) (i j : I → A) (r : I) :
    ringMap f (xvw i j r) = xvw (f ∘ i) (f ∘ j) r := by
  rw [xvw, xvw, map_mul, map_commutatorElement, ringMap_rowProd, ringMap_colProd, ringMap_rowProd,
    comp_smul, Function.comp_apply]

theorem ringMap_xz (f : A →+* B) {i w : I → A} {t : I} (hwi : w ⬝ᵥ i = 0) (ht : w t = 0) :
    ringMap f (xz i w) = xz (f ∘ i) (f ∘ w) := by
  have hwi' : (f ∘ w) ⬝ᵥ (f ∘ i) = 0 := by rw [← RingHom.map_dotProduct, hwi, map_zero]
  have ht' : (f ∘ w) t = 0 := by rw [Function.comp_apply, ht, map_zero]
  rw [xz_eq hwi ht, xz_eq hwi' ht', ringMap_xvw]

theorem map_single_one (f : A →+* B) (p t : I) : f ((Pi.single p (1 : A) : I → A) t) = (Pi.single p (1 : B) : I → B) t := by
  by_cases h : t = p
  · rw [h, Pi.single_eq_same, Pi.single_eq_same, map_one]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, map_zero]

theorem comp_vdkPiece (f : A →+* B) (i j k : I → A) (p q : I) :
    (f ∘ vdkPiece i j k p q : I → B) = vdkPiece (f ∘ i) (f ∘ j) (f ∘ k) p q := by
  funext t
  simp only [Function.comp_apply, vdkPiece_apply, map_sub, map_mul, map_single_one]

theorem ringMap_piece (h4 : 4 ≤ Fintype.card I) (f : A →+* B) (i j k : I → A) (x : I × I) :
    ringMap f (xz i (piece i j k x)) = xz (f ∘ i) (piece (f ∘ i) (f ∘ j) (f ∘ k) x) := by
  obtain ⟨t, htp, htq, -⟩ := exists_ne_three h4 x.1 x.2 x.1
  rw [ringMap_xz f (vdkPiece_dotProduct i j k x.1 x.2) (vdkPiece_apply_of_ne i j k htp htq)]
  exact congrArg (xz (f ∘ i)) (comp_vdkPiece f i j k x.1 x.2)

theorem ringMap_xk (h4 : 4 ≤ Fintype.card I) (f : A →+* B) (i j k : I → A) :
    ringMap f (xk h4 i j k) = xk h4 (f ∘ i) (f ∘ j) (f ∘ k) := by
  have hL : ∀ L : List (I × I), ringMap f (L.map fun x => xz i (piece i j k x)).prod =
      (L.map fun x => xz (f ∘ i) (piece (f ∘ i) (f ∘ j) (f ∘ k) x)).prod := by
    intro L
    induction L with
    | nil => rw [List.map_nil, List.map_nil, List.prod_nil, List.prod_nil, map_one]
    | cons x L ih =>
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, map_mul, ih,
        ringMap_piece h4 f i j k x]
  rw [xk_eq_list_prod h4 i j k (Finset.nodup_toList _) (Finset.toList_toFinset _),
    xk_eq_list_prod h4 (f ∘ i) (f ∘ j) (f ∘ k) (Finset.nodup_toList _)
      (Finset.toList_toFinset _), hL]

/-- **Naturality.** For a ring map `f : A →+* B`, `ringMap f` sends `X(v, w)` to
`X(f ∘ v, f ∘ w)`. -/
theorem elements_natural (h4 : 4 ≤ Fintype.card I) (f : A →+* B) {v w : I → A}
    (h : (v, w) ∈ U I A) (h' : (f ∘ v, f ∘ w) ∈ U I B) :
    ringMap f ((elements I A h4).elt (v, w) h) = (elements I B h4).elt (f ∘ v, f ∘ w) h' := by
  show ringMap f (eltOf h4 (v, w) h) = eltOf h4 (f ∘ v, f ∘ w) h'
  apply eq_eltOf_of_mem_Xbar
  have hji : (f ∘ w) ⬝ᵥ (f ∘ v) = 0 := by
    rw [← RingHom.map_dotProduct, (mem_U.1 h).2, map_zero]
  have hk : (f ∘ unitRow (mem_U.1 h).1) ⬝ᵥ (f ∘ v) = 1 := by
    rw [← RingHom.map_dotProduct, unitRow_spec, map_one]
  rw [eltOf, ringMap_xk]
  exact xk_mem_Xbar h4 hji hk

#audit_axioms elements_natural

end VdK
end K2Found
end BooneHigmanLinear
end GroupApproximation
