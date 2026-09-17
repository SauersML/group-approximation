import GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.CommutatorCalculus
import GroupApproximation.Steinberg.KervaireSteinberg
import GroupApproximation.PropertyT.FreeAlgebraDegree
import Mathlib.GroupTheory.FinitelyPresentedGroup
import GroupApproximation.Meta.AxiomGuard

/-!
# A finite presentation candidate for `St_5(ℤ⟨X⟩)`

For an alphabet `X`, the group `KMGroup X` has one generator `g(i, j, s)` for every pair of
indices `i, j : Fin 5` and every `s : Option X`.  The generator `g(i, j, none)` stands for the
Steinberg generator `x_{ij}(1)`, and `g(i, j, some a)` stands for `x_{ij}(a)`.  The relators are:

* `g(i, i, s) = 1`;
* `⁅g(i, j, s), g(k, l, t)⁆ = 1` when `i ≠ j`, `k ≠ l`, `j ≠ k` and `i ≠ l`;
* `⁅g(i, j, none), g(j, k, t)⁆ = g(i, k, t)` when `i, j, k` are distinct;
* `⁅g(i, j, some a), g(j, k, none)⁆ = g(i, k, some a)` when `i, j, k` are distinct.

For finite `X` there are finitely many generators and relators, so `KMGroup X` is finitely
presented.  This module builds the presentation and the homomorphism `φ : KMGroup X → St_5(ℤ⟨X⟩)`,
and computes `φ` on the iterated commutator words `word X u i j`, which represent `x_{ij}` of the
monomial `u`.  The inverse homomorphism and the isomorphism are in `LeavittFP.RootExtension`.
-/

namespace GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

open scoped commutatorElement
open FreeAlgebraDegree

noncomputable section

variable (X : Type*)

/-! ## Generators and relators -/

/-- Generators: an ordered pair of indices and an optional letter. -/
abbrev Gen := Fin 5 × Fin 5 × Option X

/-- Index data of the commutation relators. -/
abbrev R1Dom :=
  {q : Gen X × Gen X // q.1.1 ≠ q.1.2.1 ∧ q.2.1 ≠ q.2.2.1 ∧ q.1.2.1 ≠ q.2.1 ∧ q.1.1 ≠ q.2.2.1}

/-- Index data of the adjacent relators with unit left entry. -/
abbrev R2Dom :=
  {q : Fin 5 × Fin 5 × Fin 5 × Option X // q.1 ≠ q.2.1 ∧ q.2.1 ≠ q.2.2.1 ∧ q.1 ≠ q.2.2.1}

/-- Index data of the adjacent relators with a letter as left entry. -/
abbrev R3Dom :=
  {q : Fin 5 × Fin 5 × Fin 5 × X // q.1 ≠ q.2.1 ∧ q.2.1 ≠ q.2.2.1 ∧ q.1 ≠ q.2.2.1}

/-- Diagonal generators are trivial. -/
def r0 (p : Fin 5 × Option X) : FreeGroup (Gen X) :=
  FreeGroup.of (p.1, p.1, p.2)

/-- Commutation relators. -/
def r1 (q : R1Dom X) : FreeGroup (Gen X) :=
  ⁅FreeGroup.of q.1.1, FreeGroup.of q.1.2⁆

/-- Adjacent relators `⁅g(i, j, none), g(j, k, t)⁆ g(i, k, t)⁻¹`. -/
def r2 (q : R2Dom X) : FreeGroup (Gen X) :=
  ⁅FreeGroup.of ((q.1.1, q.1.2.1, none) : Gen X), FreeGroup.of ((q.1.2.1, q.1.2.2.1, q.1.2.2.2) : Gen X)⁆ *
    (FreeGroup.of ((q.1.1, q.1.2.2.1, q.1.2.2.2) : Gen X))⁻¹

/-- Adjacent relators `⁅g(i, j, some a), g(j, k, none)⁆ g(i, k, some a)⁻¹`. -/
def r3 (q : R3Dom X) : FreeGroup (Gen X) :=
  ⁅FreeGroup.of ((q.1.1, q.1.2.1, some q.1.2.2.2) : Gen X),
      FreeGroup.of ((q.1.2.1, q.1.2.2.1, none) : Gen X)⁆ *
    (FreeGroup.of ((q.1.1, q.1.2.2.1, some q.1.2.2.2) : Gen X))⁻¹

/-- The relator set. -/
def rels : Set (FreeGroup (Gen X)) :=
  Set.range (r0 X) ∪ Set.range (r1 X) ∪ Set.range (r2 X) ∪ Set.range (r3 X)

instance rels_finite [Finite X] : Finite ↥(rels X) :=
  ((((Set.finite_range (r0 X)).union (Set.finite_range (r1 X))).union
    (Set.finite_range (r2 X))).union (Set.finite_range (r3 X))).to_subtype

/-- The presented group. -/
abbrev KMGroup := PresentedGroup (rels X)

/-- For finite `X`, the presented group is finitely presented. -/
theorem kmGroup_isFinitelyPresented [Finite X] : Group.IsFinitelyPresented (KMGroup X) :=
  inferInstance

/-- The generator `g(i, j, s)`. -/
def gen (i j : Fin 5) (s : Option X) : KMGroup X :=
  PresentedGroup.of ((i, j, s) : Gen X)

/-! ## The relations in `KMGroup X` -/

theorem gen_diag (i : Fin 5) (s : Option X) : gen X i i s = 1 := by
  have h : FreeGroup.of ((i, i, s) : Gen X) ∈ rels X :=
    Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_range_self (f := r0 X) (i, s))))
  exact PresentedGroup.one_of_mem h

theorem gen_commute (i j k l : Fin 5) (s t : Option X) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hil : i ≠ l) : Commute (gen X i j s) (gen X k l t) := by
  have h : ⁅FreeGroup.of ((i, j, s) : Gen X), FreeGroup.of ((k, l, t) : Gen X)⁆ ∈ rels X :=
    Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_right _
      (Set.mem_range_self (f := r1 X) (⟨((i, j, s), (k, l, t)), hij, hkl, hjk, hil⟩ : R1Dom X))))
  have h1 := PresentedGroup.one_of_mem h
  rw [map_commutatorElement] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem gen_adj_none (i j k : Fin 5) (t : Option X) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ⁅gen X i j none, gen X j k t⁆ = gen X i k t := by
  have h : ⁅FreeGroup.of ((i, j, none) : Gen X), FreeGroup.of ((j, k, t) : Gen X)⁆ *
      (FreeGroup.of ((i, k, t) : Gen X))⁻¹ ∈ rels X :=
    Set.mem_union_left _ (Set.mem_union_right _
      (Set.mem_range_self (f := r2 X) (⟨(i, j, k, t), hij, hjk, hik⟩ : R2Dom X)))
  have h1 := PresentedGroup.one_of_mem h
  rw [map_mul, map_inv, map_commutatorElement] at h1
  exact mul_inv_eq_one.mp h1

theorem gen_adj_some (i j k : Fin 5) (a : X) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ⁅gen X i j (some a), gen X j k none⁆ = gen X i k (some a) := by
  have h : ⁅FreeGroup.of ((i, j, some a) : Gen X), FreeGroup.of ((j, k, none) : Gen X)⁆ *
      (FreeGroup.of ((i, k, some a) : Gen X))⁻¹ ∈ rels X :=
    Set.mem_union_right _
      (Set.mem_range_self (f := r3 X) (⟨(i, j, k, a), hij, hjk, hik⟩ : R3Dom X))
  have h1 := PresentedGroup.one_of_mem h
  rw [map_mul, map_inv, map_commutatorElement] at h1
  exact mul_inv_eq_one.mp h1

/-! ## Spare indices and iterated commutator words -/

/-- An index different from `i` and `j`. -/
def spare (i j : Fin 5) : Fin 5 :=
  Classical.choose (KervaireSteinberg.fin_exists_spare_index le_rfl i j i j)

theorem spare_ne_left (i j : Fin 5) : spare i j ≠ i :=
  (Classical.choose_spec (KervaireSteinberg.fin_exists_spare_index le_rfl i j i j)).1

theorem spare_ne_right (i j : Fin 5) : spare i j ≠ j :=
  (Classical.choose_spec (KervaireSteinberg.fin_exists_spare_index le_rfl i j i j)).2.1

/-- The word representing `x_{ij}(a₁ ⋯ aₙ)`: `x_{ij}(1)` for the empty word, and
`⁅x_{ip}(a₁), x_{pj}(a₂ ⋯ aₙ)⁆` with `p = spare i j` otherwise. -/
def word : List X → Fin 5 → Fin 5 → KMGroup X
  | [], i, j => gen X i j none
  | a :: u, i, j => ⁅gen X i (spare i j) (some a), word u (spare i j) j⁆

theorem word_nil (i j : Fin 5) : word X [] i j = gen X i j none := rfl

theorem word_cons (a : X) (u : List X) (i j : Fin 5) :
    word X (a :: u) i j = ⁅gen X i (spare i j) (some a), word X u (spare i j) j⁆ := rfl

/-! ## The homomorphism to `St_5(ℤ⟨X⟩)` -/

/-- The coefficient of a generator. -/
def coef : Option X → FreeAlgebra ℤ X
  | none => 1
  | some a => FreeAlgebra.ι ℤ a

theorem coef_none : coef X none = 1 := rfl

theorem coef_some (a : X) : coef X (some a) = FreeAlgebra.ι ℤ a := rfl

/-- Images of the generators. -/
def phiGen (g : Gen X) : SteinbergGroup (Fin 5) (FreeAlgebra ℤ X) :=
  if h : g.1 = g.2.1 then 1 else SteinbergGroup.x g.1 g.2.1 h (coef X g.2.2)

theorem phiGen_diag (i : Fin 5) (s : Option X) : phiGen X (i, i, s) = 1 := by
  unfold phiGen
  exact dif_pos rfl

theorem phiGen_of_ne (i j : Fin 5) (s : Option X) (h : i ≠ j) :
    phiGen X (i, j, s) = SteinbergGroup.x i j h (coef X s) := by
  unfold phiGen
  exact dif_neg h

theorem phi_rels : ∀ r ∈ rels X, FreeGroup.lift (phiGen X) r = 1 := by
  intro r hr
  rcases hr with ((⟨⟨i, s⟩, rfl⟩ | ⟨⟨⟨⟨i, j, s⟩, ⟨k, l, t⟩⟩, hij, hkl, hjk, hil⟩, rfl⟩) |
      ⟨⟨⟨i, j, k, t⟩, hij, hjk, hik⟩, rfl⟩) | ⟨⟨⟨i, j, k, a⟩, hij, hjk, hik⟩, rfl⟩
  · change FreeGroup.lift (phiGen X) (FreeGroup.of ((i, i, s) : Gen X)) = 1
    rw [FreeGroup.lift_apply_of]
    exact phiGen_diag X i s
  · change FreeGroup.lift (phiGen X)
      ⁅FreeGroup.of ((i, j, s) : Gen X), FreeGroup.of ((k, l, t) : Gen X)⁆ = 1
    simp only [map_commutatorElement, FreeGroup.lift_apply_of]
    rw [phiGen_of_ne X i j s hij, phiGen_of_ne X k l t hkl]
    exact (SteinbergGroup.x_commute_of_ne i j k l hij hkl hjk (Ne.symm hil) _ _).commutator_eq
  · change FreeGroup.lift (phiGen X)
      (⁅FreeGroup.of ((i, j, none) : Gen X), FreeGroup.of ((j, k, t) : Gen X)⁆ *
        (FreeGroup.of ((i, k, t) : Gen X))⁻¹) = 1
    simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
    rw [phiGen_of_ne X i j none hij, phiGen_of_ne X j k t hjk, phiGen_of_ne X i k t hik,
      SteinbergGroup.x_commutator i j k hij hjk hik, coef_none, one_mul (coef X t),
      mul_inv_cancel]
  · change FreeGroup.lift (phiGen X)
      (⁅FreeGroup.of ((i, j, some a) : Gen X), FreeGroup.of ((j, k, none) : Gen X)⁆ *
        (FreeGroup.of ((i, k, some a) : Gen X))⁻¹) = 1
    simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
    rw [phiGen_of_ne X i j (some a) hij, phiGen_of_ne X j k none hjk,
      phiGen_of_ne X i k (some a) hik, SteinbergGroup.x_commutator i j k hij hjk hik, coef_none,
      mul_one (coef X (some a)), mul_inv_cancel]

/-- The homomorphism `φ : KMGroup X → St_5(ℤ⟨X⟩)`. -/
def phi : KMGroup X →* SteinbergGroup (Fin 5) (FreeAlgebra ℤ X) :=
  PresentedGroup.toGroup (phi_rels X)

theorem phi_gen (i j : Fin 5) (s : Option X) (h : i ≠ j) :
    phi X (gen X i j s) = SteinbergGroup.x i j h (coef X s) := by
  change PresentedGroup.toGroup (phi_rels X) (PresentedGroup.of ((i, j, s) : Gen X)) = _
  rw [PresentedGroup.toGroup.of]
  exact phiGen_of_ne X i j s h

/-- `φ` sends the word of `u` to the Steinberg generator of the monomial `u`. -/
theorem phi_word (u : List X) (i j : Fin 5) (h : i ≠ j) :
    phi X (word X u i j) = SteinbergGroup.x i j h (wordMonomial X ℤ (FreeMonoid.ofList u)) := by
  induction u generalizing i j with
  | nil =>
      rw [word_nil, phi_gen X i j none h, coef_none, FreeMonoid.ofList_nil, wordMonomial_one]
  | cons a u ih =>
      have hip : i ≠ spare i j := (spare_ne_left i j).symm
      have hpj : spare i j ≠ j := spare_ne_right i j
      rw [word_cons, map_commutatorElement, phi_gen X i (spare i j) (some a) hip,
        ih (spare i j) j hpj, SteinbergGroup.x_commutator i (spare i j) j hip hpj h, coef_some,
        FreeMonoid.ofList_cons, ← wordMonomial_mul, wordMonomial_of]

end

end GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP

#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.Gen
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.R1Dom
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.R2Dom
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.R3Dom
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.r0
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.r1
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.r2
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.r3
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.rels
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.rels_finite
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.KMGroup
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.kmGroup_isFinitelyPresented
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.gen
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.gen_diag
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.gen_commute
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.gen_adj_none
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.gen_adj_some
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.spare
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.spare_ne_left
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.spare_ne_right
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.word
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.word_nil
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.word_cons
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.coef
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.coef_none
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.coef_some
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.phiGen
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.phiGen_diag
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.phiGen_of_ne
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.phi_rels
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.phi
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.phi_gen
#audit_axioms GroupApproximation.Manuscript.SimpleKazhdanSofic.LeavittFP.phi_word
