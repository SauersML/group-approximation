import GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.Limit
import GroupApproximation.Steinberg.Basic
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.RingTheory.Ideal.BigOperators
import GroupApproximation.Meta.AxiomGuard

/-!
# Steinberg words over a graded ring: the homomorphism out of `St_N(B)` (lane pal-q111, H.L2)

The ring of Tulenbaev (§3) and Lavrenov–Sinchuk (§5) is `B = A[X⁻¹] + 𝔄[X] ⊆ A[X, X⁻¹]`: the Laurent
polynomials whose coefficients in positive degree lie in the ideal `𝔄` (`horrB`).  The monomial
`c Tⁿ` has `t`-degree `-n` (`t = X⁻¹`), so it is allowed exactly when `Allowed 𝔄 (-n) c`.

* `GoodFam 𝔄 Y`: `Y` satisfies the homogeneous Steinberg relations of every degree.
* `gradedHom 𝔄 Y : St_N(B) →* G` for a good family: `x_ij(b) ↦ ∏ₙ Y^{-n}_ij(bₙ)`, the product
  over the monomials of `b` (`psi`).  The factors commute, so the product lives in a commutative
  subgroup `rootSub` and is taken there.
* `gradedHom_single`: `x_ij(c Tⁿ) ↦ Y^{-n}_ij(c)`.
* `exists_hom_of_rels_one`: **Tulenbaev, Lemma 3.3**.  For `N ≥ 5`, a family satisfying the
  homogeneous relations of degree `≤ 1` gives a homomorphism `St_N(B) → G` with
  `x_ij(c Tⁿ) ↦ Y^{-n}_ij(c)` whenever `-n ≤ 1`.
-/

namespace GroupApproximation
namespace BooneHigmanLinear
namespace TulenbaevHorrocks
namespace Graded

open scoped commutatorElement

/-! ### The ring `B = A[X⁻¹] + 𝔄[X]` -/

section Ring

variable {A : Type} [CommRing A] (𝔄 : Ideal A)

/-- The coefficients of `f` in positive degree lie in `𝔄`. -/
def InHorrB (f : LaurentPolynomial A) : Prop :=
  ∀ n : ℤ, 0 < n → f.coeff n ∈ 𝔄

variable {𝔄}

theorem InHorrB.add {f g : LaurentPolynomial A} (hf : InHorrB 𝔄 f) (hg : InHorrB 𝔄 g) :
    InHorrB 𝔄 (f + g) := fun n hn => by
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  exact 𝔄.add_mem (hf n hn) (hg n hn)

theorem InHorrB.neg {f : LaurentPolynomial A} (hf : InHorrB 𝔄 f) : InHorrB 𝔄 (-f) := fun n hn => by
  rw [AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply]
  exact 𝔄.neg_mem (hf n hn)

theorem inHorrB_zero : InHorrB 𝔄 (0 : LaurentPolynomial A) := fun n _ => by
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  exact 𝔄.zero_mem

theorem inHorrB_single {n : ℤ} {c : A} (hc : Allowed 𝔄 (-n) c) :
    InHorrB 𝔄 (AddMonoidAlgebra.single n c) := fun k hk => by
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with hnk
  · exact hc (by omega)
  · exact 𝔄.zero_mem

theorem inHorrB_one : InHorrB 𝔄 (1 : LaurentPolynomial A) := by
  rw [AddMonoidAlgebra.one_def]
  exact inHorrB_single (allowed_of_nonneg (by omega) _)

theorem InHorrB.mul {f g : LaurentPolynomial A} (hf : InHorrB 𝔄 f) (hg : InHorrB 𝔄 g) :
    InHorrB 𝔄 (f * g) := by
  intro n hn
  rw [AddMonoidAlgebra.coeff_mul]
  unfold Finsupp.sum
  refine Ideal.sum_mem _ fun a _ => Ideal.sum_mem _ fun b _ => ?_
  split_ifs with hab
  · by_cases ha : 0 < a
    · exact 𝔄.mul_mem_right _ (hf a ha)
    · exact 𝔄.mul_mem_left _ (hg b (by omega))
  · exact 𝔄.zero_mem

variable (𝔄) in
/-- **`B = A[X⁻¹] + 𝔄[X]`** inside `A[X, X⁻¹]`. -/
def horrB : Subring (LaurentPolynomial A) where
  carrier := {f | InHorrB 𝔄 f}
  mul_mem' := fun hf hg => InHorrB.mul hf hg
  one_mem' := inHorrB_one
  add_mem' := fun hf hg => InHorrB.add hf hg
  zero_mem' := inHorrB_zero
  neg_mem' := fun hf => InHorrB.neg hf

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.horrB

theorem mem_horrB {f : LaurentPolynomial A} : f ∈ horrB 𝔄 ↔ InHorrB 𝔄 f :=
  Iff.rfl

theorem single_mem_horrB {n : ℤ} {c : A} (hc : Allowed 𝔄 (-n) c) :
    AddMonoidAlgebra.single n c ∈ horrB 𝔄 :=
  inHorrB_single hc

theorem allowed_coeff {f : LaurentPolynomial A} (hf : f ∈ horrB 𝔄) (n : ℤ) :
    Allowed 𝔄 (-n) (f.coeff n) :=
  fun h => hf n (by omega)

theorem sum_single_eq (f : LaurentPolynomial A) :
    f = ∑ n ∈ f.coeff.support, AddMonoidAlgebra.single n (f.coeff n) := by
  have h := AddMonoidAlgebra.sum_coeff_single f
  unfold Finsupp.sum at h
  exact h.symm

/-- Induction over the monomials of an element of `B` (use as `induction f, hf using horrB_induction`). -/
theorem horrB_induction {motive : (f : LaurentPolynomial A) → f ∈ horrB 𝔄 → Prop}
    (zero : motive 0 (horrB 𝔄).zero_mem)
    (monomial : ∀ (n : ℤ) (c : A) (hc : Allowed 𝔄 (-n) c),
      motive (AddMonoidAlgebra.single n c) (single_mem_horrB hc))
    (add : ∀ (f g : LaurentPolynomial A) (hf : f ∈ horrB 𝔄) (hg : g ∈ horrB 𝔄),
      motive f hf → motive g hg → motive (f + g) ((horrB 𝔄).add_mem hf hg))
    {f : LaurentPolynomial A} (hf : f ∈ horrB 𝔄) : motive f hf := by
  classical
  have key : ∀ s : Finset ℤ, ∃ h : (∑ n ∈ s, AddMonoidAlgebra.single n (f.coeff n)) ∈ horrB 𝔄,
      motive _ h := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      exact ⟨_, zero⟩
    | insert a s ha ih =>
      obtain ⟨h, hm⟩ := ih
      rw [Finset.sum_insert ha]
      exact ⟨_, add _ _ _ h (monomial a _ (allowed_coeff hf a)) hm⟩
  have transport : ∀ (g : LaurentPolynomial A), g = f → ∀ hg : g ∈ horrB 𝔄, motive g hg →
      motive f hf := by
    rintro g rfl hg hm
    exact hm
  obtain ⟨h, hm⟩ := key f.coeff.support
  exact transport _ (sum_single_eq f).symm h hm

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.horrB_induction

end Ring

/-! ### Good families -/

section Good

variable {A : Type} [CommRing A] (𝔄 : Ideal A) {G : Type*} [Group G] {N : ℕ}

/-- `Y` satisfies the homogeneous Steinberg relations of every degree. -/
class GoodFam (Y : Fam G A N) : Prop where
  rels : ∀ m : ℤ, Rels 𝔄 Y m

variable {𝔄} {Y : Fam G A N}

theorem all_commute [GoodFam 𝔄 Y] {i j k l : Fin N} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k)
    (hil : i ≠ l) {d e : ℤ} {c c' : A} (hc : Allowed 𝔄 d c) (hc' : Allowed 𝔄 e c') :
    Commute (Y i j hij d c) (Y k l hkl e c') :=
  (GoodFam.rels (𝔄 := 𝔄) (Y := Y) (max d e)).commute hij hkl hjk hil (le_max_left d e)
    (le_max_right d e) hc hc'

theorem all_r2 [GoodFam 𝔄 Y] {i j k : Fin N} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {d e : ℤ} {c c' : A} (hc : Allowed 𝔄 d c) (hc' : Allowed 𝔄 e c') :
    ⁅Y i j hij d c, Y j k hjk e c'⁆ = Y i k hik (d + e) (c * c') :=
  (GoodFam.rels (𝔄 := 𝔄) (Y := Y) (max (max d e) (d + e))).r2 i j k hij hjk hik d e c c'
    ((le_max_left d e).trans (le_max_left _ _)) ((le_max_right d e).trans (le_max_left _ _))
    (le_max_right _ _) hc hc'

theorem all_add [GoodFam 𝔄 Y] {i j : Fin N} (hij : i ≠ j) {d : ℤ} {c c' : A}
    (hc : Allowed 𝔄 d c) (hc' : Allowed 𝔄 d c') :
    Y i j hij d c * Y i j hij d c' = Y i j hij d (c + c') :=
  (GoodFam.rels (𝔄 := 𝔄) (Y := Y) d).add i j hij d c c' le_rfl hc hc'

theorem all_one [GoodFam 𝔄 Y] {i j : Fin N} (hij : i ≠ j) (d : ℤ) : Y i j hij d 0 = 1 :=
  (GoodFam.rels (𝔄 := 𝔄) (Y := Y) d).one hij le_rfl

variable (𝔄 Y)

/-- The images of the root elements of `x_ij`. -/
def rootSet (i j : Fin N) (hij : i ≠ j) : Set G :=
  {g | ∃ (d : ℤ) (c : A), Allowed 𝔄 d c ∧ Y i j hij d c = g}

/-- The subgroup they generate. -/
def rootSub (i j : Fin N) (hij : i ≠ j) : Subgroup G :=
  Subgroup.closure (rootSet 𝔄 Y i j hij)

variable {𝔄 Y}

theorem commute_of_mem_closure' {s t : Set G} (h : ∀ x ∈ s, ∀ y ∈ t, Commute x y) {g k : G}
    (hg : g ∈ Subgroup.closure s) (hk : k ∈ Subgroup.closure t) : Commute g k := by
  have ht : Subgroup.closure t ≤ Subgroup.centralizer s := by
    rw [Subgroup.closure_le]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro x hx
    exact (h x hx y hy).eq
  have hs : Subgroup.closure s ≤ Subgroup.centralizer (Subgroup.closure t : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    exact ((Subgroup.mem_centralizer_iff.mp (ht hy)) x hx).symm
  exact ((Subgroup.mem_centralizer_iff.mp (hs hg)) k hk).symm

/-- Root subgroups commute under the conditions of the third Steinberg relation. -/
theorem rootSub_commute [GoodFam 𝔄 Y] {i j k l : Fin N} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hil : i ≠ l) {x y : G} (hx : x ∈ rootSub 𝔄 Y i j hij)
    (hy : y ∈ rootSub 𝔄 Y k l hkl) : Commute x y := by
  refine commute_of_mem_closure' ?_ hx hy
  rintro _ ⟨d, c, hc, rfl⟩ _ ⟨e, c', hc', rfl⟩
  exact all_commute hij hkl hjk hil hc hc'

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.rootSub_commute

instance rootSub_commGroup [GoodFam 𝔄 Y] (i j : Fin N) (hij : i ≠ j) :
    CommGroup (rootSub 𝔄 Y i j hij) :=
  { (inferInstance : Group (rootSub 𝔄 Y i j hij)) with
    mul_comm := fun a b => Subtype.ext (rootSub_commute hij hij hij.symm hij a.2 b.2).eq }

variable (𝔄 Y)

/-- The root element `Y^{-n}_ij(c)` as an element of the root subgroup (`1` if not allowed). -/
noncomputable def gB (i j : Fin N) (hij : i ≠ j) (n : ℤ) (c : A) : rootSub 𝔄 Y i j hij := by
  classical
  exact if h : Allowed 𝔄 (-n) c then ⟨Y i j hij (-n) c, Subgroup.subset_closure ⟨-n, c, h, rfl⟩⟩
    else 1

variable {𝔄 Y}

theorem gB_coe {i j : Fin N} (hij : i ≠ j) {n : ℤ} {c : A} (h : Allowed 𝔄 (-n) c) :
    (gB 𝔄 Y i j hij n c : G) = Y i j hij (-n) c := by
  unfold gB
  rw [dif_pos h]

theorem gB_zero [GoodFam 𝔄 Y] {i j : Fin N} (hij : i ≠ j) (n : ℤ) :
    gB 𝔄 Y i j hij n 0 = 1 := by
  apply Subtype.ext
  rw [gB_coe hij (allowed_zero _), all_one (𝔄 := 𝔄) hij, Subgroup.coe_one]

theorem gB_add [GoodFam 𝔄 Y] {i j : Fin N} (hij : i ≠ j) {n : ℤ} {c c' : A}
    (hc : Allowed 𝔄 (-n) c) (hc' : Allowed 𝔄 (-n) c') :
    gB 𝔄 Y i j hij n (c + c') = gB 𝔄 Y i j hij n c * gB 𝔄 Y i j hij n c' := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, gB_coe hij (hc.add hc'), gB_coe hij hc, gB_coe hij hc',
    all_add hij hc hc']

variable (𝔄 Y)

/-- `∏ₙ Y^{-n}_ij(fₙ)`, in the root subgroup. -/
noncomputable def psiH [GoodFam 𝔄 Y] (i j : Fin N) (hij : i ≠ j) (f : LaurentPolynomial A) :
    rootSub 𝔄 Y i j hij :=
  ∏ n ∈ f.coeff.support, gB 𝔄 Y i j hij n (f.coeff n)

/-- `∏ₙ Y^{-n}_ij(fₙ)`, in `G`. -/
noncomputable def psi [GoodFam 𝔄 Y] (i j : Fin N) (hij : i ≠ j) (f : LaurentPolynomial A) : G :=
  (psiH 𝔄 Y i j hij f : G)

variable {𝔄 Y}

theorem psiH_eq_of_subset [GoodFam 𝔄 Y] {i j : Fin N} (hij : i ≠ j) (f : LaurentPolynomial A)
    {S : Finset ℤ} (hS : f.coeff.support ⊆ S) :
    psiH 𝔄 Y i j hij f = ∏ n ∈ S, gB 𝔄 Y i j hij n (f.coeff n) := by
  unfold psiH
  refine Finset.prod_subset hS fun n _ hn => ?_
  rw [Finsupp.notMem_support_iff.mp hn, gB_zero hij]

theorem psiH_zero [GoodFam 𝔄 Y] {i j : Fin N} (hij : i ≠ j) :
    psiH 𝔄 Y i j hij 0 = 1 := by
  unfold psiH
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.support_zero, Finset.prod_empty]

theorem psiH_add [GoodFam 𝔄 Y] {i j : Fin N} (hij : i ≠ j) {f g : LaurentPolynomial A}
    (hf : f ∈ horrB 𝔄) (hg : g ∈ horrB 𝔄) :
    psiH 𝔄 Y i j hij (f + g) = psiH 𝔄 Y i j hij f * psiH 𝔄 Y i j hij g := by
  classical
  have hfg : (f + g).coeff.support ⊆ f.coeff.support ∪ g.coeff.support := by
    rw [AddMonoidAlgebra.coeff_add]
    exact Finsupp.support_add
  have h1 : f.coeff.support ⊆ f.coeff.support ∪ g.coeff.support := Finset.subset_union_left
  have h2 : g.coeff.support ⊆ f.coeff.support ∪ g.coeff.support := Finset.subset_union_right
  rw [psiH_eq_of_subset hij (f + g) hfg, psiH_eq_of_subset hij f h1, psiH_eq_of_subset hij g h2,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun n _ => ?_
  rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
    gB_add hij (allowed_coeff hf n) (allowed_coeff hg n)]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.psiH_add

theorem psiH_single [GoodFam 𝔄 Y] {i j : Fin N} (hij : i ≠ j) (n : ℤ) (c : A) :
    psiH 𝔄 Y i j hij (AddMonoidAlgebra.single n c) = gB 𝔄 Y i j hij n c := by
  have hS : (AddMonoidAlgebra.single n c : LaurentPolynomial A).coeff.support ⊆ {n} := by
    rw [AddMonoidAlgebra.coeff_single]
    exact Finsupp.support_single_subset
  rw [psiH_eq_of_subset hij _ hS, Finset.prod_singleton, AddMonoidAlgebra.coeff_single,
    Finsupp.single_eq_same]

theorem psi_mem [GoodFam 𝔄 Y] {i j : Fin N} (hij : i ≠ j) (f : LaurentPolynomial A) :
    psi 𝔄 Y i j hij f ∈ rootSub 𝔄 Y i j hij :=
  (psiH 𝔄 Y i j hij f).2

theorem psi_zero [GoodFam 𝔄 Y] {i j : Fin N} (hij : i ≠ j) : psi 𝔄 Y i j hij 0 = 1 := by
  unfold psi
  rw [psiH_zero hij, Subgroup.coe_one]

theorem psi_add [GoodFam 𝔄 Y] {i j : Fin N} (hij : i ≠ j) {f g : LaurentPolynomial A}
    (hf : f ∈ horrB 𝔄) (hg : g ∈ horrB 𝔄) :
    psi 𝔄 Y i j hij (f + g) = psi 𝔄 Y i j hij f * psi 𝔄 Y i j hij g := by
  unfold psi
  rw [psiH_add hij hf hg, Subgroup.coe_mul]

theorem psi_single [GoodFam 𝔄 Y] {i j : Fin N} (hij : i ≠ j) {n : ℤ} {c : A}
    (hc : Allowed 𝔄 (-n) c) : psi 𝔄 Y i j hij (AddMonoidAlgebra.single n c) = Y i j hij (-n) c := by
  unfold psi
  rw [psiH_single hij n c, gB_coe hij hc]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.psi_single

/-- **The second Steinberg relation for `psi`**. -/
theorem psi_comm [GoodFam 𝔄 Y] {i j k : Fin N} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    {f g : LaurentPolynomial A} (hf : f ∈ horrB 𝔄) (hg : g ∈ horrB 𝔄) :
    ⁅psi 𝔄 Y i j hij f, psi 𝔄 Y j k hjk g⁆ = psi 𝔄 Y i k hik (f * g) := by
  -- the case of a monomial `f`
  have hmono : ∀ (n : ℤ) (c : A), Allowed 𝔄 (-n) c →
      ⁅Y i j hij (-n) c, psi 𝔄 Y j k hjk g⁆ =
        psi 𝔄 Y i k hik (AddMonoidAlgebra.single n c * g) := by
    intro n c hc
    induction g, hg using horrB_induction with
    | zero => rw [psi_zero hjk, commutatorElement_one_right, mul_zero, psi_zero hik]
    | monomial n' c' hc' =>
      have hnn : Allowed 𝔄 (-(n + n')) (c * c') := by
        rw [neg_add]
        exact hc.mul hc'
      rw [psi_single hjk hc', all_r2 hij hjk hik hc hc', AddMonoidAlgebra.single_mul_single,
        psi_single hik hnn, neg_add]
    | add g₁ g₂ hg₁ hg₂ h₁ h₂ =>
      rw [psi_add hjk hg₁ hg₂, comm_mul_right', h₁, h₂, mul_add,
        psi_add hik ((horrB 𝔄).mul_mem (single_mem_horrB hc) hg₁)
          ((horrB 𝔄).mul_mem (single_mem_horrB hc) hg₂)]
      have hc2 : Commute (psi 𝔄 Y j k hjk g₁)
          (psi 𝔄 Y i k hik (AddMonoidAlgebra.single n c * g₂)) :=
        rootSub_commute hjk hik hik.symm hjk (psi_mem hjk g₁) (psi_mem hik _)
      rw [mul_assoc, mul_assoc, ← mul_assoc (psi 𝔄 Y j k hjk g₁), conj_eq_of_commute hc2]
  induction f, hf using horrB_induction with
  | zero => rw [psi_zero hij, commutatorElement_one_left, zero_mul, psi_zero hik]
  | monomial n c hc =>
    rw [psi_single hij hc]
    exact hmono n c hc
  | add f₁ f₂ hf₁ hf₂ h₁ h₂ =>
    rw [psi_add hij hf₁ hf₂, comm_mul_left', h₁, h₂, add_mul,
      psi_add hik ((horrB 𝔄).mul_mem hf₁ hg) ((horrB 𝔄).mul_mem hf₂ hg)]
    have hc2 : Commute (psi 𝔄 Y i j hij f₁) (psi 𝔄 Y i k hik (f₂ * g)) :=
      rootSub_commute hij hik hij.symm hik (psi_mem hij f₁) (psi_mem hik _)
    rw [conj_eq_of_commute hc2]
    exact ((rootSub_commute hik hik hik.symm hik (psi_mem hik _) (psi_mem hik _)).eq).symm

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.psi_comm

variable (𝔄 Y)

/-- The images of the Steinberg generators of `St_N(B)`. -/
noncomputable def psiGen [GoodFam 𝔄 Y] (g : SteinbergGenerator (Fin N) (horrB 𝔄)) : G :=
  psi 𝔄 Y g.row g.column g.row_ne_column (g.coefficient : LaurentPolynomial A)

private theorem psiGen_kills_relations [GoodFam 𝔄 Y]
    (w : FreeGroup (SteinbergGenerator (Fin N) (horrB 𝔄)))
    (hw : w ∈ SteinbergGroup.relations (I := Fin N) (R := horrB 𝔄)) :
    FreeGroup.lift (psiGen 𝔄 Y) w = 1 := by
  change SteinbergGroup.IsRelation w at hw
  cases hw with
  | add i j hij a b =>
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of, psiGen]
      change psi 𝔄 Y i j hij (a : LaurentPolynomial A) * psi 𝔄 Y i j hij (b : LaurentPolynomial A) *
        (psi 𝔄 Y i j hij ((a + b : horrB 𝔄) : LaurentPolynomial A))⁻¹ = 1
      rw [Subring.coe_add, psi_add hij a.2 b.2, mul_inv_cancel]
  | commute i j k l hij hkl hjk hli a b =>
      simp only [map_commutatorElement, FreeGroup.lift_apply_of, psiGen]
      change ⁅psi 𝔄 Y i j hij (a : LaurentPolynomial A), psi 𝔄 Y k l hkl (b : LaurentPolynomial A)⁆ = 1
      exact comm_eq_one_of_commute
        (rootSub_commute hij hkl hjk hli.symm (psi_mem hij _) (psi_mem hkl _))
  | adjacent i j k hij hjk hik a b =>
      simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of, psiGen]
      change ⁅psi 𝔄 Y i j hij (a : LaurentPolynomial A), psi 𝔄 Y j k hjk (b : LaurentPolynomial A)⁆ *
        (psi 𝔄 Y i k hik ((a * b : horrB 𝔄) : LaurentPolynomial A))⁻¹ = 1
      rw [Subring.coe_mul, psi_comm hij hjk hik a.2 b.2, mul_inv_cancel]

/-- **The homomorphism `St_N(B) →* G`** of a good family. -/
noncomputable def gradedHom [GoodFam 𝔄 Y] : SteinbergGroup (Fin N) (horrB 𝔄) →* G :=
  PresentedGroup.toGroup (f := psiGen 𝔄 Y) (psiGen_kills_relations 𝔄 Y)

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.gradedHom

variable {𝔄 Y}

theorem gradedHom_x [GoodFam 𝔄 Y] (i j : Fin N) (hij : i ≠ j) (b : horrB 𝔄) :
    gradedHom 𝔄 Y (SteinbergGroup.x i j hij b) = psi 𝔄 Y i j hij (b : LaurentPolynomial A) :=
  PresentedGroup.toGroup.of _

theorem gradedHom_single [GoodFam 𝔄 Y] (i j : Fin N) (hij : i ≠ j) {n : ℤ} {c : A}
    (hc : Allowed 𝔄 (-n) c) :
    gradedHom 𝔄 Y (SteinbergGroup.x i j hij ⟨AddMonoidAlgebra.single n c, single_mem_horrB hc⟩) =
      Y i j hij (-n) c := by
  rw [gradedHom_x]
  exact psi_single hij hc

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.gradedHom_single

end Good

/-! ### Tulenbaev, Lemma 3.3 -/

section Main

variable {A : Type} [CommRing A] {𝔄 : Ideal A} {G : Type*} [Group G] {N : ℕ}

/-- **Tulenbaev, Lemma 3.3; Lavrenov–Sinchuk, Prop 5.3.**  For `N ≥ 5`, let `Y` satisfy the
homogeneous Steinberg relations of degree `≤ 1` over `B = A[X⁻¹] + 𝔄[X]`.  Then there is a
homomorphism `St_N(B) → G` sending `x_ij(c Tⁿ)` to `Y^{-n}_ij(c)` whenever `-n ≤ 1`. -/
theorem exists_hom_of_rels_one {Y : Fam G A N} (h : Rels 𝔄 Y 1) (hN5 : 5 ≤ N) :
    ∃ φ : SteinbergGroup (Fin N) (horrB 𝔄) →* G, ∀ (i j : Fin N) (hij : i ≠ j) (n : ℤ) (c : A)
      (hc : Allowed 𝔄 (-n) c), -n ≤ 1 →
        φ (SteinbergGroup.x i j hij ⟨AddMonoidAlgebra.single n c, single_mem_horrB hc⟩) =
          Y i j hij (-n) c := by
  have hN : 3 ≤ N := by omega
  haveI : GoodFam 𝔄 (limit hN Y) := ⟨h.limit hN hN5⟩
  refine ⟨gradedHom 𝔄 (limit hN Y), fun i j hij n c hc hn => ?_⟩
  rw [gradedHom_single i j hij hc, limit_of_le_one hN Y hij hn]

#audit_axioms GroupApproximation.BooneHigmanLinear.TulenbaevHorrocks.Graded.exists_hom_of_rels_one

end Main

end Graded
end TulenbaevHorrocks
end BooneHigmanLinear
end GroupApproximation
