import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVRefine.Descend
import GroupApproximation.Manuscript.SimpleKazhdanSofic.Full.LVRefine.Vectors

/-!
# The refinement homomorphism intertwines the vector actions

`simple_kazhdan_sofic_group.tex`, l.733-735 (`sec:questions`), cites Caprace--Rémy for infinite
finitely presented simple Kazhdan groups. On the Leavitt route to that claim, Khanh's Theorem 5.4
(arXiv:2609.08428, tex l.527-556) needs that `D_r : St_n(R) → St_{n+1}(R)` covers a conjugation
of elementary matrices.

We prove it in coordinates: `vecAct (refineHom L r g) (splitVec L r v) = splitVec L r (vecAct g v)`
(`vecAct_refineHom`). It is checked on generators (`vecAct_refineRoot`, in three cases) and then
extended through the subgroup `intertwiners L r` of all elements with this property.
-/

namespace GroupApproximation
namespace Full
namespace LVRefine

open SteinbergGroup

variable {R : Type*} [Ring R] (L : LeavittFamily R) {n : ℕ} (r : Fin n)

/-- Generator case `X_{rj}(a)` of the intertwining identity. -/
theorem vecAct_refineRoot_row (j : Fin n) (hrj : r ≠ j) (a : R) (v : Fin n → R) :
    vecAct (refineRoot L r r j hrj a) (splitVec L r v) = splitVec L r (vecAct (x r j hrj a) v) := by
  have hjr : j ≠ r := fun e => hrj e.symm
  rw [refineRoot_of_row L r hrj a rfl, vecAct_mul]
  funext p
  induction p using Fin.lastCases with
  | last =>
      rw [vecAct_x_apply_of_ne _ _ _ _ _ (Fin.castSucc_ne_last r).symm, vecAct_x_apply_self,
        splitVec_castSucc_of_ne L r v hjr, splitVec_last, splitVec_last, vecAct_x_apply_self,
        mul_add, mul_assoc]
  | cast k =>
      by_cases hk : k = r
      · rw [hk, vecAct_x_apply_self, vecAct_x_apply_of_ne _ _ _ _ _ (Fin.castSucc_ne_last r),
          vecAct_x_apply_of_ne _ _ _ _ _ (Fin.castSucc_ne_last j), splitVec_castSucc_self,
          splitVec_castSucc_of_ne L r v hjr, splitVec_castSucc_self, vecAct_x_apply_self, mul_add,
          mul_assoc]
      · rw [vecAct_x_apply_of_ne _ _ _ _ _ (cs_ne hk),
          vecAct_x_apply_of_ne _ _ _ _ _ (Fin.castSucc_ne_last k), splitVec_castSucc_of_ne L r v hk,
          splitVec_castSucc_of_ne L r _ hk, vecAct_x_apply_of_ne _ _ _ _ _ hk]

/-- Generator case `X_{ir}(a)` of the intertwining identity; it uses `s0 t0 + s1 t1 = 1`. -/
theorem vecAct_refineRoot_col (i : Fin n) (hir : i ≠ r) (a : R) (v : Fin n → R) :
    vecAct (refineRoot L r i r hir a) (splitVec L r v) = splitVec L r (vecAct (x i r hir a) v) := by
  have hri : r ≠ i := fun e => hir e.symm
  rw [refineRoot_of_col L r hir a hir rfl, vecAct_mul]
  funext p
  induction p using Fin.lastCases with
  | last =>
      rw [vecAct_x_apply_of_ne _ _ _ _ _ (Fin.castSucc_ne_last i).symm,
        vecAct_x_apply_of_ne _ _ _ _ _ (Fin.castSucc_ne_last i).symm, splitVec_last, splitVec_last,
        vecAct_x_apply_of_ne _ _ _ _ _ hri]
  | cast k =>
      by_cases hki : k = i
      · rw [hki, vecAct_x_apply_self, vecAct_x_apply_self,
          vecAct_x_apply_of_ne _ _ _ _ _ (cs_ne hri), splitVec_castSucc_of_ne L r v hir,
          splitVec_last, splitVec_castSucc_self, splitVec_castSucc_of_ne L r _ hir,
          vecAct_x_apply_self, add_assoc, split_coeff]
      · by_cases hkr : k = r
        · rw [hkr, vecAct_x_apply_of_ne _ _ _ _ _ (cs_ne hri),
            vecAct_x_apply_of_ne _ _ _ _ _ (cs_ne hri), splitVec_castSucc_self,
            splitVec_castSucc_self, vecAct_x_apply_of_ne _ _ _ _ _ hri]
        · rw [vecAct_x_apply_of_ne _ _ _ _ _ (cs_ne hki),
            vecAct_x_apply_of_ne _ _ _ _ _ (cs_ne hki), splitVec_castSucc_of_ne L r v hkr,
            splitVec_castSucc_of_ne L r _ hkr, vecAct_x_apply_of_ne _ _ _ _ _ hki]

/-- Generator case `X_{ij}(a)` with `i, j ≠ r` of the intertwining identity. -/
theorem vecAct_refineRoot_plain {i j : Fin n} (hij : i ≠ j) (a : R) (v : Fin n → R)
    (hir : i ≠ r) (hjr : j ≠ r) :
    vecAct (refineRoot L r i j hij a) (splitVec L r v) = splitVec L r (vecAct (x i j hij a) v) := by
  have hri : r ≠ i := fun e => hir e.symm
  rw [refineRoot_of_plain L r hij a hir hjr]
  funext p
  induction p using Fin.lastCases with
  | last =>
      rw [vecAct_x_apply_of_ne _ _ _ _ _ (Fin.castSucc_ne_last i).symm, splitVec_last,
        splitVec_last, vecAct_x_apply_of_ne _ _ _ _ _ hri]
  | cast k =>
      by_cases hki : k = i
      · rw [hki, vecAct_x_apply_self, splitVec_castSucc_of_ne L r v hir,
          splitVec_castSucc_of_ne L r v hjr, splitVec_castSucc_of_ne L r _ hir,
          vecAct_x_apply_self]
      · by_cases hkr : k = r
        · rw [hkr, vecAct_x_apply_of_ne _ _ _ _ _ (cs_ne hri), splitVec_castSucc_self,
            splitVec_castSucc_self, vecAct_x_apply_of_ne _ _ _ _ _ hri]
        · rw [vecAct_x_apply_of_ne _ _ _ _ _ (cs_ne hki), splitVec_castSucc_of_ne L r v hkr,
            splitVec_castSucc_of_ne L r _ hkr, vecAct_x_apply_of_ne _ _ _ _ _ hki]

/-- The refined generators intertwine the vector actions (Khanh Thm 5.4,
`eq:steinberg-refinement`; `sec:questions` l.733-735). -/
theorem vecAct_refineRoot (i j : Fin n) (hij : i ≠ j) (a : R) (v : Fin n → R) :
    vecAct (refineRoot L r i j hij a) (splitVec L r v) = splitVec L r (vecAct (x i j hij a) v) := by
  by_cases hi : i = r
  · subst hi
    exact vecAct_refineRoot_row L _ _ hij a v
  · by_cases hj : j = r
    · subst hj
      exact vecAct_refineRoot_col L _ _ hij a v
    · exact vecAct_refineRoot_plain L r hij a v hi hj

/-- The subgroup of `St_n(R)` on which `refineHom L r` intertwines the vector actions. -/
def intertwiners : Subgroup (SteinbergGroup (Fin n) R) where
  carrier := {g | ∀ v, vecAct (refineHom L r g) (splitVec L r v) = splitVec L r (vecAct g v)}
  one_mem' := by
    intro v
    rw [map_one, vecAct_one, vecAct_one]
  mul_mem' := by
    intro g h hg hh v
    rw [map_mul, vecAct_mul, vecAct_mul, hh v, hg (vecAct h v)]
  inv_mem' := by
    intro g hg v
    have h1 := hg (vecAct g⁻¹ v)
    rw [← vecAct_mul, mul_inv_cancel, vecAct_one] at h1
    rw [← h1, ← vecAct_mul, ← map_mul (refineHom L r), inv_mul_cancel, map_one, vecAct_one]

theorem mem_intertwiners {g : SteinbergGroup (Fin n) R} :
    g ∈ intertwiners L r ↔
      ∀ v, vecAct (refineHom L r g) (splitVec L r v) = splitVec L r (vecAct g v) :=
  Iff.rfl

/-- `D_r` intertwines the vector actions: `D_r(g) (T v) = T (g v)` for the Leavitt splitting `T`
of the coordinate `r` (Khanh Thm 5.4; `sec:questions` l.733-735). -/
theorem vecAct_refineHom (g : SteinbergGroup (Fin n) R) (v : Fin n → R) :
    vecAct (refineHom L r g) (splitVec L r v) = splitVec L r (vecAct g v) := by
  refine (mem_intertwiners L r).mp ?_ v
  refine PresentedGroup.generated_by (SteinbergGroup.relations (I := Fin n) (R := R))
    (intertwiners L r) ?_ g
  rintro ⟨i, j, hij, a⟩
  refine (mem_intertwiners L r).mpr fun w => ?_
  change vecAct (refineHom L r (x i j hij a)) (splitVec L r w) =
    splitVec L r (vecAct (x i j hij a) w)
  rw [refineHom_x]
  exact vecAct_refineRoot L r i j hij a w

end LVRefine
end Full
end GroupApproximation
