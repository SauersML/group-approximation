import GroupApproximation.ThompsonOre.PositiveFrame
import GroupApproximation.ThompsonOre.ShiftCount
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.Positivity

/-!
# Guba's Theorem 3.18: `(1 - x_0) K[G] ∩ b K[G] ≠ 0`

Let `P` be a positive frame of `G` (Thompson's group `F` with `x_0, x_1, …`) and `K` a field.
For every `b ∈ K[G]` there is `v ≠ 0` with `b v ∈ (1 - x_0) K[G]`.

The proof is the shift argument.  Translate the support of `b` on the right by `g`, so that
each `s g` is `x_0^(k_s) w_s` with `w_s` a word in the letters `x_(i+1)`.  Test elements
`w_i = x_0^n σ`, with `n ≤ N` and `σ` a sorted word of length `c` in `L` letters, satisfy
`s g w_i = x_0^(k_s + n) u_(s,i)` with `u_(s,i) = φ^n(w_s) σ` a sorted word of length between
`c` and `c + D`.  Modulo `(1 - x_0) K[G]`, the element `b g w_i` is `Ψ_i = ∑ b_s u_(s,i)`.  The
`Ψ_i` live in a space of dimension `∑_(d ≤ D) multichoose L (c + d)`, which is smaller than the
number `(N + 1) multichoose L c` of indices, so some nontrivial combination `∑ r_i Ψ_i` vanishes,
and `v = g ∑ r_i w_i` works.

* `PositiveFrame.exists_ne_zero_one_sub_x_zero_mul_eq_mul`: the theorem for every `b`.
* `PositiveFrame.exists_mul_ne_zero_one_sub_x_zero_mul_eq_mul`: with no zero divisors and
  `b ≠ 0`, the common multiple `b v` is nonzero.
-/

namespace GroupApproximation.ThompsonOre

open MonoidAlgebra

section OneSubMul

variable {K G : Type*} [Ring K] [Group G]

/-- `y` is a right multiple of `1 - h`. -/
def OneSubMul (h : G) (y : MonoidAlgebra K G) : Prop :=
  ∃ u, (1 - of K G h) * u = y

theorem oneSubMul_zero (h : G) : OneSubMul h (0 : MonoidAlgebra K G) := ⟨0, mul_zero _⟩

theorem OneSubMul.add {h : G} {y z : MonoidAlgebra K G} (hy : OneSubMul h y)
    (hz : OneSubMul h z) : OneSubMul h (y + z) := by
  obtain ⟨u, rfl⟩ := hy
  obtain ⟨w, rfl⟩ := hz
  exact ⟨u + w, mul_add _ _ _⟩

theorem OneSubMul.neg {h : G} {y : MonoidAlgebra K G} (hy : OneSubMul h y) :
    OneSubMul h (-y) := by
  obtain ⟨u, rfl⟩ := hy
  exact ⟨-u, mul_neg _ _⟩

theorem oneSubMul_sum {ι : Type*} (h : G) (s : Finset ι) (f : ι → MonoidAlgebra K G)
    (hf : ∀ i ∈ s, OneSubMul h (f i)) : OneSubMul h (∑ i ∈ s, f i) :=
  Finset.sum_induction f (OneSubMul h) (fun _ _ => OneSubMul.add) (oneSubMul_zero h) hf

/-- `c g - c h^n g` is a right multiple of `1 - h`. -/
theorem oneSubMul_single_sub (h g : G) (c : K) (n : ℕ) :
    OneSubMul h (single g c - single (h ^ n * g) c) := by
  refine ⟨(∑ i ∈ Finset.range n, of K G h ^ i) * single g c, ?_⟩
  rw [← mul_assoc, mul_neg_geom_sum, sub_mul, one_mul]
  simp [single_pow, single_mul_single]

end OneSubMul

section SortSym

/-- The sorted list of the letters of a multiset of `n` letters from `Fin L`. -/
def sortSym {L n : ℕ} (a : Sym (Fin L) n) : List ℕ :=
  ((a : Multiset (Fin L)).map Fin.val).sort (· ≤ ·)

theorem sortSym_sorted {L n : ℕ} (a : Sym (Fin L) n) : (sortSym a).Pairwise (· ≤ ·) :=
  Multiset.pairwise_sort _ _

theorem length_sortSym {L n : ℕ} (a : Sym (Fin L) n) : (sortSym a).length = n := by
  rw [sortSym, Multiset.length_sort, Multiset.card_map, Sym.card_coe]

theorem lt_of_mem_sortSym {L n : ℕ} (a : Sym (Fin L) n) : ∀ y ∈ sortSym a, y < L := by
  intro y hy
  rw [sortSym, Multiset.mem_sort, Multiset.mem_map] at hy
  obtain ⟨z, -, rfl⟩ := hy
  exact z.isLt

theorem sortSym_injective {L n : ℕ} : Function.Injective (sortSym (L := L) (n := n)) := by
  intro a₁ a₂ h
  have h' : ((sortSym a₁ : List ℕ) : Multiset ℕ) = (sortSym a₂ : Multiset ℕ) := by rw [h]
  simp only [sortSym, Multiset.sort_eq] at h'
  exact Sym.coe_injective (Multiset.map_injective Fin.val_injective h')

theorem map_val_pmap_mk {L : ℕ} : ∀ (m : List ℕ) (hL : ∀ y ∈ m, y < L),
    (m.pmap (fun y hy => (⟨y, hy⟩ : Fin L)) hL).map Fin.val = m
  | [], _ => rfl
  | y :: m, hL => by
    simp only [List.pmap_cons, List.map_cons, map_val_pmap_mk m]

theorem exists_sortSym_eq {L n : ℕ} (m : List ℕ) (hm : m.Pairwise (· ≤ ·))
    (hL : ∀ y ∈ m, y < L) (hn : m.length = n) : ∃ a : Sym (Fin L) n, sortSym a = m := by
  refine ⟨Sym.mk (m.pmap (fun y hy => (⟨y, hy⟩ : Fin L)) hL : Multiset (Fin L))
    (by rw [Multiset.coe_card, List.length_pmap, hn]), ?_⟩
  rw [sortSym, Sym.coe_mk, Multiset.map_coe, map_val_pmap_mk, Multiset.coe_sort]
  exact List.mergeSort_eq_self _ hm

end SortSym

theorem lt_sum_add_one_of_mem : ∀ (l : List ℕ) (y : ℕ), y ∈ l → y < l.sum + 1
  | [], y, hy => by simp at hy
  | a :: l, y, hy => by
    rw [List.sum_cons]
    rcases List.mem_cons.mp hy with rfl | hy
    · omega
    · have := lt_sum_add_one_of_mem l y hy
      omega

namespace PositiveFrame

variable {K G : Type*} [Field K] [Group G] (P : PositiveFrame G)

/-- The shift argument with explicit bounds: the letters of the `w_s` are below `I`, their
lengths at most `D`, and `N`, `c`, `L` satisfy the counting inequalities. -/
theorem exists_oneSubMul_of_bounds (b : MonoidAlgebra K G) (g : G) (kf : G → ℕ)
    (lf : G → List ℕ) (hkl : ∀ s ∈ b.coeff.support, s * g = P.x 0 ^ kf s * P.word 1 (lf s))
    {I D N c L : ℕ} (hI : ∀ s ∈ b.coeff.support, ∀ y ∈ lf s, y < I)
    (hD : ∀ s ∈ b.coeff.support, (lf s).length ≤ D) (hN : (D + 1) * 3 ^ D ≤ N) (hL : 1 ≤ L)
    (hLc : L ≤ 2 * c + 3) (hIL : I + N + D + c ≤ L) :
    ∃ v : MonoidAlgebra K G, v ≠ 0 ∧ OneSubMul (P.x 0) (b * v) := by
  classical
  obtain ⟨w, hw_def⟩ : ∃ w : Fin (N + 1) × Sym (Fin L) c → G,
      ∀ i, w i = P.x 0 ^ (i.1 : ℕ) * P.word 1 (sortSym i.2) :=
    ⟨fun i => P.x 0 ^ (i.1 : ℕ) * P.word 1 (sortSym i.2), fun _ => rfl⟩
  obtain ⟨u, hu_def⟩ : ∃ u : G → Fin (N + 1) × Sym (Fin L) c → G,
      ∀ s i, u s i = P.word 1 (mergeWords ((lf s).map (· + (i.1 : ℕ))) (sortSym i.2)) :=
    ⟨fun s i => P.word 1 (mergeWords ((lf s).map (· + (i.1 : ℕ))) (sortSym i.2)),
      fun _ _ => rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : Finset G, W = (Finset.range (D + 1)).biUnion fun d =>
      (Finset.univ : Finset (Sym (Fin L) (c + d))).image fun a => P.word 1 (sortSym a) :=
    ⟨_, rfl⟩
  have hsw : ∀ s ∈ b.coeff.support, ∀ i,
      s * (g * w i) = P.x 0 ^ (kf s + (i.1 : ℕ)) * u s i := by
    intro s hs i
    rw [← mul_assoc, hkl s hs, hw_def, hu_def]
    exact P.pow_mul_word_mul_pow_mul_word (kf s) i.1 (lf s) (sortSym i.2)
  have hw : Function.Injective w := by
    intro i j hij
    rw [hw_def, hw_def] at hij
    obtain ⟨h1, h2⟩ := P.pow_mul_word_inj (sortSym_sorted i.2) (sortSym_sorted j.2) hij
    exact Prod.ext (Fin.ext h1) (sortSym_injective h2)
  -- every `u_(s,i)` is a sorted word of length between `c` and `c + D` in `L` letters
  have huW : ∀ s ∈ b.coeff.support, ∀ i, u s i ∈ W := by
    intro s hs i
    have hsorted := mergeWords_sorted ((lf s).map (· + (i.1 : ℕ))) (sortSym i.2)
      (sortSym_sorted i.2)
    have hlt : ∀ y ∈ mergeWords ((lf s).map (· + (i.1 : ℕ))) (sortSym i.2), y < L := by
      refine mem_mergeWords_lt _ _ (fun y hy => ?_) (lt_of_mem_sortSym i.2)
      obtain ⟨y', hy', hyy⟩ := List.mem_map.mp hy
      have e : y = y' + (i.1 : ℕ) := hyy.symm
      have h1 := hI s hs y' hy'
      have h2 := hD s hs
      have h3 := i.1.isLt
      rw [List.length_map, length_sortSym]
      omega
    obtain ⟨a, ha⟩ := exists_sortSym_eq (n := c + (lf s).length) _ hsorted hlt
      (by rw [length_mergeWords, List.length_map, length_sortSym]; omega)
    rw [hW, hu_def]
    exact Finset.mem_biUnion.mpr ⟨(lf s).length,
      Finset.mem_range.mpr (by have := hD s hs; omega),
      Finset.mem_image.mpr ⟨a, Finset.mem_univ a, congrArg (P.word 1) ha⟩⟩
  -- the coefficients on `W` of `∑ r_i Ψ_i`, as a linear map in `r`
  let f : (Fin (N + 1) × Sym (Fin L) c → K) →ₗ[K] (W → K) :=
    { toFun := fun r y =>
        ∑ i, ∑ s ∈ b.coeff.support, (if u s i = (y : G) then b.coeff s else 0) * r i
      map_add' := fun r r' => by
        funext y
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun a r => by
        funext y
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun s _ => by ring }
  have hcard : Module.finrank K (W → K) <
      Module.finrank K (Fin (N + 1) × Sym (Fin L) c → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
      Fintype.card_coe, Fintype.card_prod, Fintype.card_fin, Sym.card_sym_fin_eq_multichoose]
    calc W.card ≤ ∑ d ∈ Finset.range (D + 1),
          ((Finset.univ : Finset (Sym (Fin L) (c + d))).image
            fun a => P.word 1 (sortSym a)).card := by
          rw [hW]; exact Finset.card_biUnion_le
      _ ≤ ∑ d ∈ Finset.range (D + 1), Nat.multichoose L (c + d) := by
          refine Finset.sum_le_sum fun d _ => Finset.card_image_le.trans ?_
          rw [Finset.card_univ, Sym.card_sym_fin_eq_multichoose]
      _ < (N + 1) * Nat.multichoose L c := sum_multichoose_lt hL hLc hN
  obtain ⟨r, hr, hr0⟩ :=
    (Submodule.ne_bot_iff _).mp (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hcard)
  rw [LinearMap.mem_ker] at hr
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hr0
  have hcoeff : ∀ y, (∑ i, ∑ s ∈ b.coeff.support, single (u s i) (b.coeff s * r i)).coeff y =
      ∑ i, ∑ s ∈ b.coeff.support, (if u s i = y then b.coeff s else 0) * r i := by
    intro y
    simp only [coeff_sum, Finsupp.finsetSum_apply, coeff_single, Finsupp.single_apply, ite_mul,
      zero_mul]
  have hΦ : ∑ i, ∑ s ∈ b.coeff.support, single (u s i) (b.coeff s * r i) =
      (0 : MonoidAlgebra K G) := by
    ext y
    rw [hcoeff, coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
    by_cases hy : y ∈ W
    · exact congrFun hr ⟨y, hy⟩
    · refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun s hs => ?_
      rw [if_neg fun h : u s i = y => hy (h ▸ huW s hs i), zero_mul]
  refine ⟨∑ i, single (g * w i) (r i), fun hv => hi₀ ?_, ?_⟩
  · have h := congrArg (fun z : MonoidAlgebra K G => z.coeff (g * w i₀)) hv
    simpa [Finsupp.single_apply, hw.eq_iff] using h
  · have hbv : b * ∑ i, single (g * w i) (r i) =
        ∑ i, ∑ s ∈ b.coeff.support, single (s * (g * w i)) (b.coeff s * r i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      conv_lhs => rw [← sum_coeff_single b]
      rw [Finsupp.sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun s _ => single_mul_single _ _ _ _
    have hsplit : b * ∑ i, single (g * w i) (r i) = ∑ i, ∑ s ∈ b.coeff.support,
        (single (s * (g * w i)) (b.coeff s * r i) - single (u s i) (b.coeff s * r i)) := by
      simp only [Finset.sum_sub_distrib, hΦ, sub_zero, hbv]
    rw [hsplit]
    refine oneSubMul_sum _ _ _ fun i _ => oneSubMul_sum _ _ _ fun s hs => ?_
    rw [hsw s hs i, ← neg_sub]
    exact (oneSubMul_single_sub (P.x 0) (u s i) (b.coeff s * r i) (kf s + (i.1 : ℕ))).neg

/-- **Guba's Theorem 3.18.** For every `b ∈ K[G]`, the equation `(1 - x_0) u = b v` has a
solution with `v ≠ 0`. -/
theorem exists_ne_zero_one_sub_x_zero_mul_eq_mul (b : MonoidAlgebra K G) :
    ∃ u v : MonoidAlgebra K G, v ≠ 0 ∧ (1 - of K G (P.x 0)) * u = b * v := by
  classical
  obtain ⟨g, hg⟩ := P.exists_mul_eq_pow_mul_word b.coeff.support
  have hg' : ∀ s : G, ∃ (k : ℕ) (l : List ℕ),
      s ∈ b.coeff.support → s * g = P.x 0 ^ k * P.word 1 l := by
    intro s
    by_cases hs : s ∈ b.coeff.support
    · obtain ⟨k, l, -, h⟩ := hg s hs
      exact ⟨k, l, fun _ => h⟩
    · exact ⟨0, [], fun h => absurd h hs⟩
  choose kf lf hkl using hg'
  obtain ⟨I, hI⟩ : ∃ I, ∀ s ∈ b.coeff.support, ∀ y ∈ lf s, y < I :=
    ⟨b.coeff.support.sup fun s => (lf s).sum + 1, fun s hs y hy =>
      (lt_sum_add_one_of_mem (lf s) y hy).trans_le
        (Finset.le_sup (f := fun s => (lf s).sum + 1) hs)⟩
  obtain ⟨D, hD⟩ : ∃ D, ∀ s ∈ b.coeff.support, (lf s).length ≤ D :=
    ⟨b.coeff.support.sup fun s => (lf s).length, fun s hs =>
      Finset.le_sup (f := fun s => (lf s).length) hs⟩
  obtain ⟨N, hN, hN1⟩ : ∃ N, (D + 1) * 3 ^ D ≤ N ∧ 1 ≤ N :=
    ⟨(D + 1) * 3 ^ D, le_rfl, (show 0 < (D + 1) * 3 ^ D by positivity)⟩
  obtain ⟨v, hv, u, hu⟩ := P.exists_oneSubMul_of_bounds b g kf lf hkl hI hD hN
    (c := I + N + D) (L := 2 * (I + N + D)) (by omega) (by omega) (by omega)
  exact ⟨u, v, hv, hu⟩

/-- With no zero divisors, a nonzero `b` has a nonzero common right multiple with `1 - x_0`.
This is the hypothesis `h318` of `one_sub_solution_of_nested`. -/
theorem exists_mul_ne_zero_one_sub_x_zero_mul_eq_mul [NoZeroDivisors (MonoidAlgebra K G)]
    (b : MonoidAlgebra K G) (hb : b ≠ 0) :
    ∃ v, b * v ≠ 0 ∧ ∃ u, b * v = (1 - of K G (P.x 0)) * u := by
  obtain ⟨u, v, hv, hu⟩ := P.exists_ne_zero_one_sub_x_zero_mul_eq_mul b
  exact ⟨v, mul_ne_zero hb hv, u, hu.symm⟩

end PositiveFrame

end GroupApproximation.ThompsonOre
