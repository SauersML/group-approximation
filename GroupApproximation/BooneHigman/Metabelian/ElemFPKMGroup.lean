import GroupApproximation.Steinberg.KervaireSteinberg
import Mathlib.GroupTheory.FinitelyPresentedGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# A finite presentation candidate for `St_{d+5}(ℤ⟨X⟩)`

This is the rank-`d + 5` generalisation of
`GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.FreePresentation` (which is the
case `d = 0`).  For an alphabet `X`, the group `KMGroup X d` has one generator `g(i, j, s)` for
every pair of indices `i, j : Fin (d + 5)` and every `s : Option X`.  The generator
`g(i, j, none)` stands for `x_{ij}(1)` and `g(i, j, some a)` stands for `x_{ij}(a)`.  Relators:

* `g(i, i, s) = 1`;
* `⁅g(i, j, s), g(k, l, t)⁆ = 1` when `i ≠ j`, `k ≠ l`, `j ≠ k` and `i ≠ l`;
* `⁅g(i, j, none), g(j, k, t)⁆ = g(i, k, t)` when `i, j, k` are distinct;
* `⁅g(i, j, some a), g(j, k, none)⁆ = g(i, k, some a)` when `i, j, k` are distinct.

For finite `X` there are finitely many generators and relators, so `KMGroup X d` is finitely
presented.  The only place where the rank matters is the existence of a spare index, which
uses `KervaireSteinberg.fin_exists_spare_index` with `5 ≤ d + 5`.
-/

namespace GroupApproximation.BooneHigman.Metabelian.ElemFP

open scoped commutatorElement

noncomputable section

variable (X : Type*) (d : ℕ)

/-! ## Generators and relators -/

/-- Generators: an ordered pair of indices and an optional letter. -/
abbrev Gen := Fin (d + 5) × Fin (d + 5) × Option X

/-- Index data of the commutation relators. -/
abbrev R1Dom :=
  {q : Gen X d × Gen X d //
    q.1.1 ≠ q.1.2.1 ∧ q.2.1 ≠ q.2.2.1 ∧ q.1.2.1 ≠ q.2.1 ∧ q.1.1 ≠ q.2.2.1}

/-- Index data of the adjacent relators with unit left entry. -/
abbrev R2Dom :=
  {q : Fin (d + 5) × Fin (d + 5) × Fin (d + 5) × Option X //
    q.1 ≠ q.2.1 ∧ q.2.1 ≠ q.2.2.1 ∧ q.1 ≠ q.2.2.1}

/-- Index data of the adjacent relators with a letter as left entry. -/
abbrev R3Dom :=
  {q : Fin (d + 5) × Fin (d + 5) × Fin (d + 5) × X //
    q.1 ≠ q.2.1 ∧ q.2.1 ≠ q.2.2.1 ∧ q.1 ≠ q.2.2.1}

/-- Diagonal generators are trivial. -/
def r0 (p : Fin (d + 5) × Option X) : FreeGroup (Gen X d) :=
  FreeGroup.of (p.1, p.1, p.2)

/-- Commutation relators. -/
def r1 (q : R1Dom X d) : FreeGroup (Gen X d) :=
  ⁅FreeGroup.of q.1.1, FreeGroup.of q.1.2⁆

/-- Adjacent relators `⁅g(i, j, none), g(j, k, t)⁆ g(i, k, t)⁻¹`. -/
def r2 (q : R2Dom X d) : FreeGroup (Gen X d) :=
  ⁅FreeGroup.of ((q.1.1, q.1.2.1, none) : Gen X d),
      FreeGroup.of ((q.1.2.1, q.1.2.2.1, q.1.2.2.2) : Gen X d)⁆ *
    (FreeGroup.of ((q.1.1, q.1.2.2.1, q.1.2.2.2) : Gen X d))⁻¹

/-- Adjacent relators `⁅g(i, j, some a), g(j, k, none)⁆ g(i, k, some a)⁻¹`. -/
def r3 (q : R3Dom X d) : FreeGroup (Gen X d) :=
  ⁅FreeGroup.of ((q.1.1, q.1.2.1, some q.1.2.2.2) : Gen X d),
      FreeGroup.of ((q.1.2.1, q.1.2.2.1, none) : Gen X d)⁆ *
    (FreeGroup.of ((q.1.1, q.1.2.2.1, some q.1.2.2.2) : Gen X d))⁻¹

/-- The relator set. -/
def rels : Set (FreeGroup (Gen X d)) :=
  Set.range (r0 X d) ∪ Set.range (r1 X d) ∪ Set.range (r2 X d) ∪ Set.range (r3 X d)

instance rels_finite [Finite X] : Finite ↥(rels X d) :=
  ((((Set.finite_range (r0 X d)).union (Set.finite_range (r1 X d))).union
    (Set.finite_range (r2 X d))).union (Set.finite_range (r3 X d))).to_subtype

/-- The presented group. -/
abbrev KMGroup := PresentedGroup (rels X d)

/-- For finite `X`, the presented group is finitely presented. -/
theorem kmGroup_isFinitelyPresented [Finite X] : Group.IsFinitelyPresented (KMGroup X d) :=
  inferInstance

/-- The generator `g(i, j, s)`. -/
def gen (i j : Fin (d + 5)) (s : Option X) : KMGroup X d :=
  PresentedGroup.of ((i, j, s) : Gen X d)

/-! ## The relations in `KMGroup X d` -/

theorem gen_diag (i : Fin (d + 5)) (s : Option X) : gen X d i i s = 1 := by
  have h : FreeGroup.of ((i, i, s) : Gen X d) ∈ rels X d :=
    Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_range_self (f := r0 X d) (i, s))))
  exact PresentedGroup.one_of_mem h

theorem gen_commute (i j k l : Fin (d + 5)) (s t : Option X) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hil : i ≠ l) : Commute (gen X d i j s) (gen X d k l t) := by
  have h : ⁅FreeGroup.of ((i, j, s) : Gen X d), FreeGroup.of ((k, l, t) : Gen X d)⁆ ∈
      rels X d :=
    Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _
      (Set.mem_range_self (f := r1 X d)
        (⟨((i, j, s), (k, l, t)), hij, hkl, hjk, hil⟩ : R1Dom X d))))
  have h1 := PresentedGroup.one_of_mem h
  rw [map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem gen_adj_none (i j k : Fin (d + 5)) (t : Option X) (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) : ⁅gen X d i j none, gen X d j k t⁆ = gen X d i k t := by
  have h : ⁅FreeGroup.of ((i, j, none) : Gen X d), FreeGroup.of ((j, k, t) : Gen X d)⁆ *
      (FreeGroup.of ((i, k, t) : Gen X d))⁻¹ ∈ rels X d :=
    Set.mem_union_left _ (Set.mem_union_right _
      (Set.mem_range_self (f := r2 X d) (⟨(i, j, k, t), hij, hjk, hik⟩ : R2Dom X d)))
  have h1 := PresentedGroup.one_of_mem h
  rw [map_mul, map_inv, map_commutatorElement] at h1
  exact mul_inv_eq_one.mp h1

theorem gen_adj_some (i j k : Fin (d + 5)) (a : X) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ⁅gen X d i j (some a), gen X d j k none⁆ = gen X d i k (some a) := by
  have h : ⁅FreeGroup.of ((i, j, some a) : Gen X d), FreeGroup.of ((j, k, none) : Gen X d)⁆ *
      (FreeGroup.of ((i, k, some a) : Gen X d))⁻¹ ∈ rels X d :=
    Set.mem_union_right _
      (Set.mem_range_self (f := r3 X d) (⟨(i, j, k, a), hij, hjk, hik⟩ : R3Dom X d))
  have h1 := PresentedGroup.one_of_mem h
  rw [map_mul, map_inv, map_commutatorElement] at h1
  exact mul_inv_eq_one.mp h1

/-! ## Spare indices and iterated commutator words -/

variable {d} in
/-- An index different from `i` and `j`. -/
def spare (i j : Fin (d + 5)) : Fin (d + 5) :=
  Classical.choose (KervaireSteinberg.fin_exists_spare_index (Nat.le_add_left 5 d) i j i j)

variable {d} in
theorem spare_ne_left (i j : Fin (d + 5)) : spare i j ≠ i :=
  (Classical.choose_spec
    (KervaireSteinberg.fin_exists_spare_index (Nat.le_add_left 5 d) i j i j)).1

variable {d} in
theorem spare_ne_right (i j : Fin (d + 5)) : spare i j ≠ j :=
  (Classical.choose_spec
    (KervaireSteinberg.fin_exists_spare_index (Nat.le_add_left 5 d) i j i j)).2.1

/-- The word representing `x_{ij}(a₁ ⋯ aₙ)`: `x_{ij}(1)` for the empty word, and
`⁅x_{ip}(a₁), x_{pj}(a₂ ⋯ aₙ)⁆` with `p = spare i j` otherwise. -/
def word : List X → Fin (d + 5) → Fin (d + 5) → KMGroup X d
  | [], i, j => gen X d i j none
  | a :: u, i, j => ⁅gen X d i (spare i j) (some a), word u (spare i j) j⁆

theorem word_nil (i j : Fin (d + 5)) : word X d [] i j = gen X d i j none := rfl

theorem word_cons (a : X) (u : List X) (i j : Fin (d + 5)) :
    word X d (a :: u) i j = ⁅gen X d i (spare i j) (some a), word X d u (spare i j) j⁆ := rfl

end

end GroupApproximation.BooneHigman.Metabelian.ElemFP

#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.Gen
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.R1Dom
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.R2Dom
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.R3Dom
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.r0
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.r1
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.r2
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.r3
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.rels
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.rels_finite
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.KMGroup
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.kmGroup_isFinitelyPresented
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.gen
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.gen_diag
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.gen_commute
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.gen_adj_none
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.gen_adj_some
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.spare
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.spare_ne_left
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.spare_ne_right
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.word
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.word_nil
#audit_axioms GroupApproximation.BooneHigman.Metabelian.ElemFP.word_cons
