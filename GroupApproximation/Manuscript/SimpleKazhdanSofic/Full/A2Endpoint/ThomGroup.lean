import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Subgroup.Simple
import GroupApproximation.Meta.AxiomGuard

/-!
# Thom's group, and why it is not simple (table row A2)

`simple_kazhdan_sofic_group.tex`, Introduction, tex l.57–60 (table row A2):

> Thom constructed a finitely generated Kazhdan group that is locally embeddable into finite
> groups but not residually finite, and so lacks the factorization property~\cite{Thom}, but his
> example is not simple.

The cited group is from A. Thom, *Examples of hyperlinear groups without factorization
property*, Groups Geom. Dyn. **4** (2010), 195–208, §2.1 ("Non-hopfian Kazhdan groups"):

> Let `R` be a (unital) commutative ring and define `G_0(R)` to be the following group of matrices:
> the matrices in `SL_5(R)` with first column `e_1` and last row `e_5ᵀ` [entries `a_{ij}` arbitrary
> otherwise]. We will be mainly interested in `G_0 = G_0(F_p[t,t⁻¹])` for some prime `p`. The
> centre `Z(G_0)` of `G_0` consists of the elementary matrices `{e_15(a) | a ∈ F_p[t,t⁻¹]}` and it
> is naturally isomorphic to `⊕_{n ∈ ℤ} F_p t^n`. We denote by `C` the subgroup corresponding to
> `⊕_{n ≥ 0} F_p t^n ⊆ Z(G_0)` and set `G = G_0/C`.

This file builds that group literally and proves the last clause of tex l.60, "his example is not
simple", by exhibiting a normal subgroup that is neither trivial nor everything.

* `thomG0 R`: the subgroup `G_0(R)` of `SL_5(R)` (indices `0,…,4` for Thom's `1,…,5`).
* `thomCentral R : Multiplicative R →* G_0(R)`, `a ↦ e_15(a)` (`Matrix.transvection 0 4 a`).
  Every element of `G_0(R)` commutes with it (`thomCentral_comm`), so every subgroup of its range
  is normal (`normal_of_le_range`).
* `thomC K`: Thom's `C`, the image of `K[t] ⊆ K[t,t⁻¹]` under `thomCentral`.
* `ThomGroup K = G_0(K[t,t⁻¹]) / C`; Thom's group is `ThomGroup (ZMod p)`.
* `thomCentreImage K`: the image `Z(G_0)/C` of all central transvections in `ThomGroup K`.
  - it is not trivial: `e_15(t⁻¹) ∉ C`, since `t⁻¹` is not a polynomial (`X` is not a unit);
  - it is not everything: the class of `e_12(1)` is not in it, since `e_15(a) e_15(b) = e_15(a+b)`
    has `(1,2)`-entry `0`.

Endpoints: `exists_normal_ne_bot_ne_top_thomGroup`, `not_isSimpleGroup_thomGroup`,
`not_isSimpleGroup_thomGroup_zmod`.
-/

namespace GroupApproximation.Full.A2Endpoint

theorem fin_zero_ne_four : (0 : Fin 5) ≠ 4 := by decide

theorem fin_zero_ne_one : (0 : Fin 5) ≠ 1 := by decide

theorem fin_one_ne_zero : (1 : Fin 5) ≠ 0 := by decide

section Shape

variable {R : Type*} [CommRing R]

/-- Thom's shape (Thom, §2.1): first column `e_1` and last row `e_5ᵀ`. -/
structure IsThomShape (M : Matrix (Fin 5) (Fin 5) R) : Prop where
  col : ∀ i, M i 0 = (1 : Matrix (Fin 5) (Fin 5) R) i 0
  row : ∀ j, M 4 j = (1 : Matrix (Fin 5) (Fin 5) R) 4 j

theorem IsThomShape.mul {M N : Matrix (Fin 5) (Fin 5) R} (hM : IsThomShape M)
    (hN : IsThomShape N) : IsThomShape (M * N) := by
  constructor
  · intro i
    calc (M * N) i 0 = (M * (1 : Matrix (Fin 5) (Fin 5) R)) i 0 := by
          simp only [Matrix.mul_apply, hN.col]
      _ = (1 : Matrix (Fin 5) (Fin 5) R) i 0 := by rw [Matrix.mul_one, hM.col]
  · intro j
    calc (M * N) 4 j = ((1 : Matrix (Fin 5) (Fin 5) R) * N) 4 j := by
          simp only [Matrix.mul_apply, hM.row]
      _ = (1 : Matrix (Fin 5) (Fin 5) R) 4 j := by rw [Matrix.one_mul, hN.row]

/-- A two-sided inverse of a matrix of Thom shape has Thom shape. -/
theorem IsThomShape.of_mul_eq_one {M N : Matrix (Fin 5) (Fin 5) R} (hM : IsThomShape M)
    (h1 : N * M = 1) (h2 : M * N = 1) : IsThomShape N := by
  constructor
  · intro i
    calc N i 0 = (N * (1 : Matrix (Fin 5) (Fin 5) R)) i 0 := by rw [Matrix.mul_one]
      _ = (N * M) i 0 := by simp only [Matrix.mul_apply, hM.col]
      _ = (1 : Matrix (Fin 5) (Fin 5) R) i 0 := by rw [h1]
  · intro j
    calc N 4 j = ((1 : Matrix (Fin 5) (Fin 5) R) * N) 4 j := by rw [Matrix.one_mul]
      _ = (M * N) 4 j := by simp only [Matrix.mul_apply, hM.row]
      _ = (1 : Matrix (Fin 5) (Fin 5) R) 4 j := by rw [h2]

/-- The elementary matrix `e_{ij}(c)` has Thom shape when `i ≠ 5` and `j ≠ 1` (Thom's indices). -/
theorem isThomShape_transvection {i j : Fin 5} (hi : i ≠ 4) (hj : j ≠ 0) (c : R) :
    IsThomShape (Matrix.transvection i j c) := by
  constructor
  · intro k
    calc Matrix.transvection i j c k 0
        = ((1 : Matrix (Fin 5) (Fin 5) R) * Matrix.transvection i j c) k 0 := by
          rw [Matrix.one_mul]
      _ = (1 : Matrix (Fin 5) (Fin 5) R) k 0 :=
          Matrix.mul_transvection_apply_of_ne i j k 0 (Ne.symm hj) c 1
  · intro l
    calc Matrix.transvection i j c 4 l
        = (Matrix.transvection i j c * (1 : Matrix (Fin 5) (Fin 5) R)) 4 l := by
          rw [Matrix.mul_one]
      _ = (1 : Matrix (Fin 5) (Fin 5) R) 4 l :=
          Matrix.transvection_mul_apply_of_ne i j 4 l (Ne.symm hi) c 1

theorem transvection_apply_self {i j : Fin 5} (h : i ≠ j) (c : R) :
    Matrix.transvection i j c i j = c := by
  calc Matrix.transvection i j c i j
      = ((1 : Matrix (Fin 5) (Fin 5) R) * Matrix.transvection i j c) i j := by
        rw [Matrix.one_mul]
    _ = (1 : Matrix (Fin 5) (Fin 5) R) i j + c * (1 : Matrix (Fin 5) (Fin 5) R) i i :=
        Matrix.mul_transvection_apply_same i j i c 1
    _ = c := by rw [Matrix.one_apply_ne h, Matrix.one_apply_eq, mul_one, zero_add]

theorem transvection_zero_four_apply_zero_one (c : R) :
    Matrix.transvection (0 : Fin 5) 4 c 0 1 = 0 := by
  calc Matrix.transvection (0 : Fin 5) 4 c 0 1
      = ((1 : Matrix (Fin 5) (Fin 5) R) * Matrix.transvection (0 : Fin 5) 4 c) 0 1 := by
        rw [Matrix.one_mul]
    _ = (1 : Matrix (Fin 5) (Fin 5) R) 0 1 :=
        Matrix.mul_transvection_apply_of_ne (0 : Fin 5) 4 (0 : Fin 5) (1 : Fin 5)
          (by decide) c 1
    _ = 0 := Matrix.one_apply_ne fin_zero_ne_one

/-- `e_15(c)` commutes with every matrix of Thom shape (Thom, §2.1: it is central in `G_0`). -/
theorem transvection_comm_of_isThomShape {M : Matrix (Fin 5) (Fin 5) R} (hM : IsThomShape M)
    (c : R) :
    Matrix.transvection (0 : Fin 5) 4 c * M = M * Matrix.transvection (0 : Fin 5) 4 c := by
  ext a b
  by_cases ha : a = 0
  · subst ha
    by_cases hb : b = 4
    · subst hb
      rw [Matrix.transvection_mul_apply_same, Matrix.mul_transvection_apply_same, hM.row, hM.col,
        Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.transvection_mul_apply_same,
        Matrix.mul_transvection_apply_of_ne (0 : Fin 5) 4 (0 : Fin 5) b hb, hM.row,
        Matrix.one_apply_ne (fun h => hb h.symm), mul_zero, add_zero]
  · by_cases hb : b = 4
    · subst hb
      rw [Matrix.transvection_mul_apply_of_ne (0 : Fin 5) 4 a (4 : Fin 5) ha,
        Matrix.mul_transvection_apply_same, hM.col, Matrix.one_apply_ne ha, mul_zero, add_zero]
    · rw [Matrix.transvection_mul_apply_of_ne (0 : Fin 5) 4 a b ha,
        Matrix.mul_transvection_apply_of_ne (0 : Fin 5) 4 a b hb]

end Shape

section G0

variable (R : Type*) [CommRing R]

/-- Thom's `G_0(R)` (Thom, §2.1): the matrices in `SL_5(R)` with first column `e_1` and last row
`e_5ᵀ`. -/
def thomG0 : Subgroup (Matrix.SpecialLinearGroup (Fin 5) R) where
  carrier := {g | IsThomShape g.1}
  mul_mem' := by
    intro a b ha hb
    have ha' : IsThomShape a.1 := ha
    have hb' : IsThomShape b.1 := hb
    show IsThomShape (a.1 * b.1)
    exact ha'.mul hb'
  one_mem' := by
    show IsThomShape (1 : Matrix (Fin 5) (Fin 5) R)
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  inv_mem' := by
    intro a ha
    have ha' : IsThomShape a.1 := ha
    have h1 : (a⁻¹).1 * a.1 = 1 := congrArg Subtype.val (inv_mul_cancel a)
    have h2 : a.1 * (a⁻¹).1 = 1 := congrArg Subtype.val (mul_inv_cancel a)
    exact ha'.of_mul_eq_one h1 h2

theorem mem_thomG0 {g : Matrix.SpecialLinearGroup (Fin 5) R} : g ∈ thomG0 R ↔ IsThomShape g.1 :=
  Iff.rfl

/-- The central transvections `a ↦ e_15(a)` of `G_0(R)` (Thom, §2.1). -/
def thomCentral : Multiplicative R →* thomG0 R where
  toFun a := ⟨⟨Matrix.transvection (0 : Fin 5) 4 (Multiplicative.toAdd a),
      Matrix.det_transvection_of_ne (0 : Fin 5) 4 fin_zero_ne_four _⟩,
    (mem_thomG0 R).2 (isThomShape_transvection fin_zero_ne_four fin_zero_ne_four.symm _)⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    exact Matrix.transvection_zero (0 : Fin 5) 4
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Matrix.transvection_mul_transvection_same (0 : Fin 5) 4 fin_zero_ne_four
      (Multiplicative.toAdd a) (Multiplicative.toAdd b)).symm

theorem thomCentral_val (a : Multiplicative R) :
    ((thomCentral R a : thomG0 R) : Matrix.SpecialLinearGroup (Fin 5) R).1 =
      Matrix.transvection (0 : Fin 5) 4 (Multiplicative.toAdd a) :=
  rfl

theorem thomCentral_comm (a : Multiplicative R) (g : thomG0 R) :
    thomCentral R a * g = g * thomCentral R a := by
  apply Subtype.ext
  apply Subtype.ext
  exact transvection_comm_of_isThomShape ((mem_thomG0 R).1 g.2) (Multiplicative.toAdd a)

/-- Every subgroup of the centre-image `{e_15(a)}` is normal in `G_0(R)`. -/
theorem normal_of_le_range {H : Subgroup (thomG0 R)} (hH : H ≤ (thomCentral R).range) :
    H.Normal :=
  ⟨fun n hn g => by
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 (hH hn)
    rw [← thomCentral_comm R a g, mul_inv_cancel_right]
    exact hn⟩

/-- The element `e_12(1)` of `G_0(R)`. -/
def thomE12 : thomG0 R :=
  ⟨⟨Matrix.transvection (0 : Fin 5) 1 (1 : R),
      Matrix.det_transvection_of_ne (0 : Fin 5) 1 fin_zero_ne_one _⟩,
    (mem_thomG0 R).2 (isThomShape_transvection fin_zero_ne_four fin_one_ne_zero _)⟩

theorem thomE12_val :
    ((thomE12 R : thomG0 R) : Matrix.SpecialLinearGroup (Fin 5) R).1 =
      Matrix.transvection (0 : Fin 5) 1 (1 : R) :=
  rfl

end G0

section Quotient

variable (K : Type*) [CommRing K]

/-- Thom's `C` (Thom, §2.1): the central transvections `e_15(a)` with `a ∈ K[t] ⊆ K[t,t⁻¹]`. -/
def thomC : Subgroup (thomG0 (LaurentPolynomial K)) :=
  ((thomCentral (LaurentPolynomial K)).comp
    (AddMonoidHom.toMultiplicative (Polynomial.toLaurent (R := K)).toAddMonoidHom)).range

theorem thomC_le_range : thomC K ≤ (thomCentral (LaurentPolynomial K)).range := by
  intro g hg
  obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hg
  exact MonoidHom.mem_range.2 ⟨_, rfl⟩

instance thomC_normal : (thomC K).Normal :=
  normal_of_le_range (LaurentPolynomial K) (thomC_le_range K)

/-- Thom's group `G = G_0(K[t,t⁻¹]) / C` (Thom, §2.1, with `K = F_p`). -/
abbrev ThomGroup : Type _ :=
  ↥(thomG0 (LaurentPolynomial K)) ⧸ thomC K

/-- The image `Z(G_0)/C` of the central transvections in Thom's group. -/
def thomCentreImage : Subgroup (ThomGroup K) :=
  (thomCentral (LaurentPolynomial K)).range.map (QuotientGroup.mk' (thomC K))

instance thomCentreImage_normal : (thomCentreImage K).Normal :=
  Subgroup.Normal.map (normal_of_le_range (LaurentPolynomial K) le_rfl) _
    (QuotientGroup.mk'_surjective (thomC K))

/-- `e_15(t⁻¹)` does not lie in `C`, so `Z(G_0)/C` is nontrivial (Thom, §2.1: the kernel of the
shift endomorphism "sits as `F_p t⁻¹` in the upper right corner of `G`"). -/
theorem thomCentreImage_ne_bot [Nontrivial K] : thomCentreImage K ≠ ⊥ := by
  intro hbot
  have hmem : QuotientGroup.mk' (thomC K) (thomCentral (LaurentPolynomial K)
      (Multiplicative.ofAdd (LaurentPolynomial.T (-1)))) ∈ thomCentreImage K :=
    Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.2 ⟨_, rfl⟩)
  rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  obtain ⟨p, hp⟩ := MonoidHom.mem_range.1 hmem
  have h04 : Polynomial.toLaurent (Multiplicative.toAdd p) =
      (LaurentPolynomial.T (-1) : LaurentPolynomial K) := by
    have h := congrArg (fun g : thomG0 (LaurentPolynomial K) => g.1.1 0 4) hp
    change Matrix.transvection (0 : Fin 5) 4 (Polynomial.toLaurent (Multiplicative.toAdd p)) 0 4 =
      Matrix.transvection (0 : Fin 5) 4 (LaurentPolynomial.T (-1) : LaurentPolynomial K) 0 4 at h
    rwa [transvection_apply_self fin_zero_ne_four, transvection_apply_self fin_zero_ne_four] at h
  have hXq : (Polynomial.X : Polynomial K) * Multiplicative.toAdd p = 1 := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, Polynomial.toLaurent_X, h04, ← LaurentPolynomial.T_add, add_neg_cancel,
      LaurentPolynomial.T_zero, Polynomial.toLaurent_one]
  exact Polynomial.not_isUnit_X
    ⟨⟨Polynomial.X, Multiplicative.toAdd p, hXq, (mul_comm _ _).trans hXq⟩, rfl⟩

/-- The class of `e_12(1)` is not in `Z(G_0)/C`, so `Z(G_0)/C` is proper. -/
theorem thomCentreImage_ne_top [Nontrivial K] : thomCentreImage K ≠ ⊤ := by
  intro htop
  have hmem : QuotientGroup.mk' (thomC K) (thomE12 (LaurentPolynomial K)) ∈ thomCentreImage K := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 hmem
  obtain ⟨z, hz, hxz⟩ := (QuotientGroup.mk'_eq_mk' (thomC K)).1 hxg
  have hg : thomE12 (LaurentPolynomial K) ∈ (thomCentral (LaurentPolynomial K)).range := by
    rw [← hxz]
    exact mul_mem hx (thomC_le_range K hz)
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hg
  have h01 := congrArg (fun g : thomG0 (LaurentPolynomial K) => g.1.1 0 1) ha
  change Matrix.transvection (0 : Fin 5) 4 (Multiplicative.toAdd a) 0 1 =
    Matrix.transvection (0 : Fin 5) 1 (1 : LaurentPolynomial K) 0 1 at h01
  rw [transvection_zero_four_apply_zero_one, transvection_apply_self fin_zero_ne_one] at h01
  exact zero_ne_one h01

/-- **tex l.60** ("his example is not simple"), explicit form: Thom's group `G_0(K[t,t⁻¹])/C` has
a normal subgroup (the image of its centre `Z(G_0)`) that is neither trivial nor everything. -/
theorem exists_normal_ne_bot_ne_top_thomGroup [Nontrivial K] :
    ∃ N : Subgroup (ThomGroup K), N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ :=
  ⟨thomCentreImage K, thomCentreImage_normal K, thomCentreImage_ne_bot K,
    thomCentreImage_ne_top K⟩

/-- **tex l.60** ("his example is not simple"): Thom's group is not a simple group. -/
theorem not_isSimpleGroup_thomGroup [Nontrivial K] : ¬ IsSimpleGroup (ThomGroup K) := by
  intro hs
  obtain ⟨N, hN, hbot, htop⟩ := exists_normal_ne_bot_ne_top_thomGroup K
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal (ThomGroup K) _ hs N hN with h | h
  · exact hbot h
  · exact htop h

end Quotient

/-- **tex l.60** for Thom's actual example `G = G_0(F_p[t,t⁻¹])/C` (Thom, §2.1). -/
theorem not_isSimpleGroup_thomGroup_zmod (p : ℕ) [Fact p.Prime] :
    ¬ IsSimpleGroup (ThomGroup (ZMod p)) :=
  not_isSimpleGroup_thomGroup (ZMod p)

#audit_axioms GroupApproximation.Full.A2Endpoint.exists_normal_ne_bot_ne_top_thomGroup
#audit_axioms GroupApproximation.Full.A2Endpoint.not_isSimpleGroup_thomGroup_zmod

end GroupApproximation.Full.A2Endpoint
